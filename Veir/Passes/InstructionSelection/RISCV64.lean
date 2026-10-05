module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.DataLayout.RISCV64
import Veir.IR.SymbolRef
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Interfaces.FunctionInterfaces
import Veir.Passes.Matching.LLVM.Basic
import Veir.Passes.InstructionSelection.Common
import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution

namespace Veir

/-!
  This file replicates LLVM's GlobalISel instruction selector,
  to lower LLVM IR to RISC-V assembly (64 bits).
-/

/-! # Lowering Patterns -/

/-- Extension operations (`sext`/`zext`) in RISC-V 64 are legal from `i8`, `i16`, and
  `i32` source widths (`zext.b`/`zext.h`/`zext.w`, `sext.b`/`sext.h`/`sext.w`).
  See: https://github.com/llvm/llvm-project/blob/16a0a1042f7e4e5a0c667096fcdeb5803e06d120/llvm/lib/Target/RISCV/GISel/RISCVLegalizerInfo.cpp#L171-L179
-/
def isLegalExtOpWidth (w : Nat) : Bool :=
  w = 8 ∨ w = 16 ∨ w = 32

/--
  Returns the bitwidth of the given type if it is either an LLVM integer or byte type.
-/
def getIntByteTypeBitwidth (t : TypeAttr) : Option Nat :=
  match t.val with
  | .integerType ⟨bw, _⟩ => some bw
  | .byteType ⟨bw⟩ => some bw
  | _ => none

/-- Whether `t` is an integer type whose width is one of `widths`. -/
def isIntTypeOfWidth (widths : List Nat) (t : TypeAttr) : Bool :=
  match t.val with
  | .integerType t => t.bitwidth ∈ widths
  | _ => false

/-- The `riscv` immediate `value`, as a 64-bit two's-complement bit pattern. -/
def mkRISCVImm (value : Int) : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (BitVec.ofInt 64 value)

/-! ## Puddle building blocks -/

/-- Puddle creation step: `builtin.unrealized_conversion_cast v : type`, returning its result. -/
def createCastP (v : Puddle.Handle OpCode .value) (type : Puddle.Handle OpCode .type) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value) := do
  let castProps ← Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
  let castOp ← Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
      #[v] #[type] castProps
  return castOp.res[0]!

/-- Puddle creation step: a `riscv` op with the already-bound properties `props` and a single
    register result, returning that result. -/
def createRiscvWithP (riscvOp : Riscv) (props : Puddle.Handle OpCode (.prop (.riscv riscvOp)))
    (operands : Array (Puddle.Handle OpCode .value)) (regType : Puddle.Handle OpCode .type) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value) := do
  let riscvResOp ← Puddle.CreateProg.operation (.riscv riscvOp) operands #[regType] props
  return riscvResOp.res[0]!

/-- Puddle creation step: a `riscv` op with properties `props` and a single register result,
    returning that result. -/
def createRiscvP (riscvOp : Riscv) (props : propertiesOf (OpCode.riscv riscvOp))
    (operands : Array (Puddle.Handle OpCode .value)) (regType : Puddle.Handle OpCode .type) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value) := do
  let riscvOpProps ← Puddle.CreateProg.property (.riscv riscvOp) props
  createRiscvWithP riscvOp riscvOpProps operands regType

/-- The value of an integer `llvm.mlir.constant` with result type `type` and properties `props`,
    read as a signed integer (as `matchConstantIntVal` does, so `i1` true is -1). -/
def constIntValue? (type : TypeAttr) (props : LLVMConstantProperties) : Option Int :=
  match type.val, props.value with
  | .integerType t, .integer attr => some (BitVec.ofInt t.bitwidth attr.value).toInt
  | _, _ => none

/-- Puddle match step: an integer `llvm.mlir.constant` whose type satisfies `typeMatcher`.
    Returns its result, its type, and its properties. -/
def matchConstantIntP (typeMatcher : IntegerType → Bool := fun _ => true) :
    Puddle.MatchProg.Builder (Puddle.Handle OpCode .value × Puddle.Handle OpCode .type ×
      Puddle.Handle OpCode (.prop (.llvm .mlir__constant))) := do
  let type ← Puddle.MatchProg.type (Attr := IntegerType) typeMatcher
  let cst ← Puddle.MatchProg.operation (.llvm .mlir__constant) #[] #[type]
    (fun props => props.value matches .integer _)
  return (cst.res[0]!, type, cst.properties)

/-- Puddle match step: an integer `llvm.mlir.constant` equal to zero (as `matchConstantZero`).
    Returns its result and its type. -/
def matchConstantZeroP :
    Puddle.MatchProg.Builder (Puddle.Handle OpCode .value × Puddle.Handle OpCode .type) := do
  let (zero, type, props) ← matchConstantIntP
  Puddle.MatchProg.matchNative (type, props) fun (type, props) => constIntValue? type props == some 0
  return (zero, type)

/--
  Shared shape of the RISC-V lowerings of a single-result LLVM op: match `llvmOp` with
  `numOperands` operands and a result type accepted by `resMatcher`, run `emit` on the operands
  (it casts them into registers as needed and returns the result register), and cast the result
  back to the result type.
-/
def lowerOpP (llvmOp : Llvm) (numOperands : Nat) (resMatcher : TypeAttr → Bool)
    (emit : Puddle.Handle OpCode .type → Array (Puddle.Handle OpCode .value) →
      Puddle.CreateProg.Builder (Puddle.Handle OpCode .value)) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let mut operands : Array (Puddle.Handle OpCode .value) := #[]
      for _ in [0:numOperands] do
        let type ← Puddle.MatchProg.type (Attr := TypeAttr)
        operands := operands.push (← Puddle.MatchProg.value type)
      let resType ← Puddle.MatchProg.type (Attr := TypeAttr) resMatcher
      let _ ← Puddle.MatchProg.root (.llvm llvmOp) operands #[resType]
      return (resType, operands))
    (fun (resType, operands) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let res ← emit regType operands
      createCastP res resType)
    (fun res => res)

/--
  Shared shape of the lowerings of single-operand LLVM ops that are no-ops on registers: when
  `legal` accepts the operand and result types, cast the operand into a register and the register
  back to the result type.
-/
def lowerRegCast (llvmOp : Llvm) (legal : TypeAttr → TypeAttr → Bool) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let opType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let resType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let x ← Puddle.MatchProg.value opType
      let _ ← Puddle.MatchProg.root (.llvm llvmOp) #[x] #[resType]
      Puddle.MatchProg.matchNative (opType, resType) fun (opType, resType) => legal opType resType
      return (resType, x))
    (fun (resType, x) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let reg ← createCastP x regType
      createCastP reg resType)
    (fun res => res)

/--
  RISC-V lowerings with Puddle for unary operations.
-/
def lowerUnary (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let returnType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let x ← Veir.Puddle.MatchProg.value returnType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[x] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[castOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[returnType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.ctlz` (`i32`) -> `riscv.clzw`. -/
def ctlz32_pattern : Veir.Puddle.Pattern OpCode := lowerUnary .intr__ctlz 32 .clzw ()

/-- `llvm.intr.ctlz` (`i64`) -> `riscv.clz`. -/
def ctlz64_pattern : Veir.Puddle.Pattern OpCode := lowerUnary .intr__ctlz 64 .clz ()

/-- `llvm.intr.cttz` (`i32`) -> `riscv.ctzw`. -/
def cttz32_pattern : Veir.Puddle.Pattern OpCode := lowerUnary .intr__cttz 32 .ctzw ()

/-- `llvm.intr.cttz` (`i64`) -> `riscv.ctz`. -/
def cttz64_pattern : Veir.Puddle.Pattern OpCode := lowerUnary .intr__cttz 64 .ctz ()

/-- `llvm.intr.ctpop` (`i32`) -> `riscv.cpopw`. -/
def ctpop32_pattern : Veir.Puddle.Pattern OpCode := lowerUnary .intr__ctpop 32 .cpopw ()

/-- `llvm.intr.ctpop` (`i64`) -> `riscv.cpop`. -/
def ctpop64_pattern : Veir.Puddle.Pattern OpCode := lowerUnary .intr__ctpop 64 .cpop ()

/--
  RISC-V lowerings with Puddle for the integer-extension operations (`sext`/`zext`): match a
  single-operand LLVM extension op whose operand has a fixed legal integer width `opBw` (`8`, `16`,
  or `32`, see `isLegalExtOpWidth`) and whose result is a strictly wider integer type of width at
  most 64 (a 64-bit register cannot represent wider results, so e.g. `sext i8 to i128` is left
  unselected; unlike `opBw`, the result width is matched generically rather than enumerated), cast
  the operand to a register, apply the byte/halfword/word extension op matching `opBw`, and cast the
  result back to the (generically-matched) result type.
-/
def lowerExt (llvmOp : Llvm) (opBw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == opBw)
      let resType ← Veir.Puddle.MatchProg.type (Attr := IntegerType)
          (fun t => opBw < t.bitwidth ∧ t.bitwidth ≤ 64)
      let x ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[castOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.sext` (`i8` operand) -> `riscv.sextb`. -/
def sext8_pattern : Veir.Puddle.Pattern OpCode := lowerExt .sext 8 .sextb ()

/-- `llvm.sext` (`i16` operand) -> `riscv.sexth`. -/
def sext16_pattern : Veir.Puddle.Pattern OpCode := lowerExt .sext 16 .sexth ()

/-- `llvm.sext` (`i32` operand) -> `riscv.sextw`. -/
def sext32_pattern : Veir.Puddle.Pattern OpCode := lowerExt .sext 32 .sextw ()

/-- `llvm.zext` (`i8` operand) -> `riscv.zextb`. -/
def zext8_pattern : Veir.Puddle.Pattern OpCode := lowerExt .zext 8 .zextb ()

/-- `llvm.zext` (`i16` operand) -> `riscv.zexth`. -/
def zext16_pattern : Veir.Puddle.Pattern OpCode := lowerExt .zext 16 .zexth ()

/-- `llvm.zext` (`i32` operand) -> `riscv.zextw`. -/
def zext32_pattern : Veir.Puddle.Pattern OpCode := lowerExt .zext 32 .zextw ()

/--
  RISC-V for binary operations that share a single integer type between both operands and the
  result: cast both operands to registers, optionally apply `extend` to each register first (e.g.
  `riscv.sextw` for the signed min/max `i32` arms, since `castToRegLocal`'s zero-extension does not
  preserve signed order), apply `riscvOp`, and cast the result back to the source type.
-/
def lowerBinary (llvmOp : Llvm) (typeMatcher : IntegerType → Bool) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp))
    (extend : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp)) := none) :
    Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) typeMatcher
      let lhs ← Veir.Puddle.MatchProg.value opType
      let rhs ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[lhs, rhs] #[opType]
      return (opType, lhs, rhs))
    (fun (opType, lhs, rhs) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let lcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let lcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType] lcastProps
      let rcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let rcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType] rcastProps
      let (lval, rval) ← match extend with
        | some ⟨extOp, extProps'⟩ => do
          let extProps ← Veir.Puddle.CreateProg.property (.riscv extOp) extProps'
          let lextOp ← Veir.Puddle.CreateProg.operation (.riscv extOp) #[lcastOp.res[0]!] #[regType] extProps
          let rextOp ← Veir.Puddle.CreateProg.operation (.riscv extOp) #[rcastOp.res[0]!] #[regType] extProps
          pure (lextOp.res[0]!, rextOp.res[0]!)
        | none => pure (lcastOp.res[0]!, rcastOp.res[0]!)
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[lval, rval] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[opType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.add` (`i64`) -> `riscv.add`. -/
def add64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .add (fun t => t.bitwidth == 64) .add ()

/-- `llvm.add` (`i32`) -> `riscv.addw` (keeps the result sign-extended). -/
def add32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .add (fun t => t.bitwidth == 32) .addw ()

/-- `llvm.sub` (`i64`) -> `riscv.sub`. -/
def sub64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .sub (fun t => t.bitwidth == 64) .sub ()

/-- `llvm.sub` (`i32`) -> `riscv.subw`. -/
def sub32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .sub (fun t => t.bitwidth == 32) .subw ()

/-- `llvm.mul` (`i64`) -> `riscv.mul`. -/
def mul64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .mul (fun t => t.bitwidth == 64) .mul ()

/-- `llvm.mul` (`i32`) -> `riscv.mulw` (sign-extends the result). -/
def mul32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .mul (fun t => t.bitwidth == 32) .mulw ()

/-- `llvm.sdiv` (`i64`) -> `riscv.div`. -/
def sdiv64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .sdiv (fun t => t.bitwidth == 64) .div ()

/-- `llvm.sdiv` (`i32`) -> `riscv.divw`. -/
def sdiv32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .sdiv (fun t => t.bitwidth == 32) .divw ()

/-- `llvm.udiv` (`i64`) -> `riscv.divu`. -/
def udiv64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .udiv (fun t => t.bitwidth == 64) .divu ()

/-- `llvm.udiv` (`i32`) -> `riscv.divuw`. -/
def udiv32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .udiv (fun t => t.bitwidth == 32) .divuw ()

/-- `llvm.srem` (`i64`) -> `riscv.rem`. -/
def srem64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .srem (fun t => t.bitwidth == 64) .rem ()

/-- `llvm.srem` (`i32`) -> `riscv.remw`. -/
def srem32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .srem (fun t => t.bitwidth == 32) .remw ()

/-- `llvm.urem` (`i64`) -> `riscv.remu`. -/
def urem64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .urem (fun t => t.bitwidth == 64) .remu ()

/-- `llvm.urem` (`i32`) -> `riscv.remuw`. -/
def urem32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .urem (fun t => t.bitwidth == 32) .remuw ()

/-- `llvm.xor` (`i64`) -> `riscv.xor`. -/
def xor64_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .xor (fun t => t.bitwidth == 64) .xor ()

/-- `llvm.xor` (`i32`) -> `riscv.xor` (no `W` variant needed: xor is bitwise). -/
def xor32_pattern : Veir.Puddle.Pattern OpCode := lowerBinary .xor (fun t => t.bitwidth == 32) .xor ()

/-- `llvm.and` -> `riscv.and` (bitwise, so one instruction for every legal width). -/
def and_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .and (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 8 ∨ t.bitwidth = 1) .and ()

/-- `llvm.or` -> `riscv.or` (bitwise, so one instruction for every legal width). -/
def or_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .or (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 8 ∨ t.bitwidth = 1) .or ()

/-- `llvm.intr.umax` -> `riscv.maxu`. Width-agnostic: unlike `add`/`sub`/…, the same instruction
    is used at both bitwidths, since the register already holds the correctly-represented value. -/
def umax_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__umax (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32) .maxu ()

/-- `llvm.intr.umin` -> `riscv.minu`. -/
def umin_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__umin (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32) .minu ()

/-- `llvm.intr.smax` (`i64`) -> `riscv.max`. -/
def smax64_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__smax (fun t => t.bitwidth == 64) .max ()

/-- `llvm.intr.smax` (`i32`) -> sign-extend (so negative values order correctly, since
    `castToRegLocal` zero-extends) then `riscv.max`. -/
def smax32_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__smax (fun t => t.bitwidth == 32) .max () (extend := some ⟨.sextw, ()⟩)

/-- `llvm.intr.smin` (`i64`) -> `riscv.min`. -/
def smin64_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__smin (fun t => t.bitwidth == 64) .min ()

/-- `llvm.intr.smin` (`i32`) -> sign-extend (so negative values order correctly, since
    `castToRegLocal` zero-extends) then `riscv.min`. -/
def smin32_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__smin (fun t => t.bitwidth == 32) .min () (extend := some ⟨.sextw, ()⟩)

/--
  RISC-V lowerings for funnel-shift rotates (`fshl`/`fshr` whose two data operands are
  identical).
-/
def lowerRotate (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let a ← Veir.Puddle.MatchProg.value opType
      let amt ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[a, a, amt] #[opType]
      return (opType, a, amt))
    (fun (opType, a, amt) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let aCastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let aCastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[a] #[regType] aCastProps
      let amtCastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let amtCastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[amt] #[regType] amtCastProps
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let rotOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[aCastOp.res[0]!, amtCastOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rotOp.res[0]!] #[opType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.fshl` with identical data operands (`i64`) -> `riscv.rol`. -/
def fshl64_pattern : Veir.Puddle.Pattern OpCode := lowerRotate .intr__fshl 64 .rol ()

/-- `llvm.intr.fshl` with identical data operands (`i32`) -> `riscv.rolw`. -/
def fshl32_pattern : Veir.Puddle.Pattern OpCode := lowerRotate .intr__fshl 32 .rolw ()

/-- `llvm.intr.fshr` with identical data operands (`i64`) -> `riscv.ror`. -/
def fshr64_pattern : Veir.Puddle.Pattern OpCode := lowerRotate .intr__fshr 64 .ror ()

/-- `llvm.intr.fshr` with identical data operands (`i32`) -> `riscv.rorw`. -/
def fshr32_pattern : Veir.Puddle.Pattern OpCode := lowerRotate .intr__fshr 32 .rorw ()

/--
  `llvm.intr.ctlz` -> `riscv.clz`.
-/
def ctlz32 : Puddle.CompiledPattern OpCode := ctlz32_pattern.compile
def ctlz64 : Puddle.CompiledPattern OpCode := ctlz64_pattern.compile

/--
  `llvm.intr.cttz` -> `riscv.ctz`.
-/
def cttz32 : Puddle.CompiledPattern OpCode := cttz32_pattern.compile
def cttz64 : Puddle.CompiledPattern OpCode := cttz64_pattern.compile

/--
  `llvm.intr.ctpop` -> `riscv.cpop`.
-/
def ctpop32 : Puddle.CompiledPattern OpCode := ctpop32_pattern.compile
def ctpop64 : Puddle.CompiledPattern OpCode := ctpop64_pattern.compile

/--
  `llvm.intr.bswap` -> `riscv.rev8`. `rev8` reverses all 8 bytes; for `i32` the wanted bytes end
  up in the high 32 bits, so shift them down with `srli 32`.
-/
def lowerBswap (bw : Nat) : Puddle.Pattern OpCode :=
  lowerOpP .intr__bswap 1 (isIntTypeOfWidth [bw]) fun regType operands => do
    let x ← createCastP operands[0]! regType
    let rev ← createRiscvP .rev8 () #[x] regType
    if bw = 32 then
      createRiscvP .srli (mkRISCVImm 32) #[rev] regType
    else
      return rev

/-- `llvm.intr.bswap` (`i64`) -> `riscv.rev8`. -/
def bswap64 : Puddle.CompiledPattern OpCode := (lowerBswap 64).compile

/-- `llvm.intr.bswap` (`i32`) -> `riscv.rev8` + `riscv.srli 32`. -/
def bswap32 : Puddle.CompiledPattern OpCode := (lowerBswap 32).compile

/--
  One SWAR bit-reversal stage:
  `((x & mask) << shamt) | ((x >> shamt) & mask)`.
-/
def bitreverseStageP (regType : Puddle.Handle OpCode .type) (mask shamt : Int)
    (input : Puddle.Handle OpCode .value) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value) := do
  let maskReg ← createRiscvP .li (mkRISCVImm mask) #[] regType
  let low ← createRiscvP .and () #[maskReg, input] regType
  let lowShift ← createRiscvP .slli (mkRISCVImm shamt) #[low] regType
  let highShift ← createRiscvP .srli (mkRISCVImm shamt) #[input] regType
  let high ← createRiscvP .and () #[maskReg, highShift] regType
  createRiscvP .or () #[lowShift, high] regType

/--
  `llvm.intr.bitreverse` -> mask/shift/or stages followed by `riscv.rev8`.
-/
def lowerBitreverse (bw : Nat) : Puddle.Pattern OpCode :=
  lowerOpP .intr__bitreverse 1 (isIntTypeOfWidth [bw]) fun regType operands => do
    let x ← createCastP operands[0]! regType
    if bw = 32 then
      /- Use 32-bit masks so SWAR stages stay within the low 32 bits.
         rev8 brings bits to high 32; srli 32 moves them back down. -/
      let x1 ← bitreverseStageP regType 0x55555555 1 x
      let x2 ← bitreverseStageP regType 0x33333333 2 x1
      let x3 ← bitreverseStageP regType 0x0f0f0f0f 4 x2
      let rev ← createRiscvP .rev8 () #[x3] regType
      createRiscvP .srli (mkRISCVImm 32) #[rev] regType
    else
      let x1 ← bitreverseStageP regType 0x5555555555555555 1 x
      let x2 ← bitreverseStageP regType 0x3333333333333333 2 x1
      let x3 ← bitreverseStageP regType 0x0f0f0f0f0f0f0f0f 4 x2
      createRiscvP .rev8 () #[x3] regType

/-- `llvm.intr.bitreverse` (`i64`) -> mask/shift/or stages followed by `riscv.rev8`. -/
def bitreverse64 : Puddle.CompiledPattern OpCode := (lowerBitreverse 64).compile

/-- `llvm.intr.bitreverse` (`i32`) -> mask/shift/or stages, `riscv.rev8` and `riscv.srli 32`. -/
def bitreverse32 : Puddle.CompiledPattern OpCode := (lowerBitreverse 32).compile

/-- llvm.constant -> riscv.li. Any width up to 64 fits in one register: the constant is
  sign-extended to the 64-bit immediate (see `constant_refinement_le64`). -/
def constant_pattern : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let type ← Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth ≤ 64)
      let root ← Puddle.MatchProg.root (.llvm .mlir__constant) #[] #[type]
        (fun props => props.value matches .integer _)
      return (type, root.properties))
    (fun (type, props) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let imm ← Puddle.CreateProg.applyNative
        (Outputs := Puddle.Handle OpCode (.prop (.riscv .li))) (type, props)
        fun (type, props) => do
          let .integerType t := type.val | none
          let .integer c := props.value | none
          return RISCVImmediateProperties.mk ((BitVec.ofInt t.bitwidth c.value).signExtend 64)
      let li ← createRiscvWithP .li imm #[] regType
      createCastP li type)
    (fun res => res)

/-- llvm.constant -> riscv.li -/
def constant : Puddle.CompiledPattern OpCode := constant_pattern.compile

/-- llvm.add -> riscv.add -/
def add64 : Puddle.CompiledPattern OpCode := add64_pattern.compile

/-- llvm.add -> riscv.addw (riscv.addw for i32, keeps the result sign-extended) -/
def add32 : Puddle.CompiledPattern OpCode := add32_pattern.compile

/-- llvm.and -> riscv.and (bitwise, so one instruction for every legal width) -/
def and : Puddle.CompiledPattern OpCode := and_pattern.compile

/--
  `llvm.ashr` -> `riscv.sra` (`riscv.sraw` for `i32`, which sign-extends the result). An `i8` lhs
  is sign-extended into the register first, so the arithmetic shift sees its sign bit.
-/
def lowerAshr (bw : Nat) : Puddle.Pattern OpCode :=
  lowerOpP .ashr 2 (isIntTypeOfWidth [bw]) fun regType operands => do
    /- First, cast the operands to registers -/
    let lhs ← createCastP operands[0]! regType
    let rhs ← createCastP operands[1]! regType
    if bw = 8 then
      let lhsExt ← createRiscvP .sextb () #[lhs] regType
      createRiscvP .sra () #[lhsExt, rhs] regType
    else if bw = 32 then
      createRiscvP .sraw () #[lhs, rhs] regType
    else
      createRiscvP .sra () #[lhs, rhs] regType

/-- llvm.ashr -> riscv.sra -/
def ashr64 : Puddle.CompiledPattern OpCode := (lowerAshr 64).compile

/-- llvm.ashr -> riscv.sraw -/
def ashr32 : Puddle.CompiledPattern OpCode := (lowerAshr 32).compile

/-- llvm.ashr -> riscv.sextb + riscv.sra -/
def ashr8 : Puddle.CompiledPattern OpCode := (lowerAshr 8).compile

/-! ### `llvm.icmp` lowering

    llvm.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1
    llvm.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs)
    llvm.icmp slt lhs rhs -> riscv.slt lhs rhs
    llvm.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1
    llvm.icmp sgt lhs rhs -> riscv.slt rhs lhs
    llvm.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1
    llvm.icmp ult lhs rhs -> riscv.sltu lhs rhs
    llvm.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1
    llvm.icmp ugt lhs rhs -> riscv.sltu rhs lhs
    llvm.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1

  Every arm shares the same prologue (`icmpCastExtP`: cast both operands into registers, and
  sign-extend them when they are narrower than a register) and the same epilogue (cast the `i1`
  result back). Only the comparison sequence in between differs (`icmpEmitP`). There is one Puddle
  pattern per predicate and lhs width, since the width selects the prologue's sign-extension. -/

/-- The `i1` constant `1`, the immediate shared by the `sltiu`/`xori` arms. -/
def icmpOneImm : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk 1#64

/-- The immediate `0`, materialized by the `li` feeding the `sltu` of the `≠` arms. -/
def icmpZeroImm : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk 0#64

/-- The sign-extension instruction needed to compare two `bw`-wide operands in a register, if any. -/
def icmpExtOf (bw : Nat) : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp)) :=
  if bw = 32 then some ⟨.sextw, ()⟩ else if bw = 8 then some ⟨.sextb, ()⟩ else none

/-- The width of an `icmp` operand of type `t` once it is in a register: integers keep their
    width, and an `!llvm.ptr` is a full 64-bit register, compared exactly like an `i64`. -/
def icmpTypeWidth? (t : TypeAttr) : Option Nat :=
  match t.val with
  | .integerType t => some t.bitwidth
  | .llvmPointerType _ => some 64
  | _ => none

/--
  Shared prologue of every `llvm.icmp` arm: cast both operands into registers and, when `ext` is
  `some e`, sign-extend each register with `e` (`riscv.sextw` for `i32`, `riscv.sextb` for `i8`).
  The cast zero-extends into the register, so without the fixup a negative narrow operand
  would look positive to the 64-bit signed comparison; sign-extension also preserves the unsigned
  order, so the unsigned comparisons stay correct too.

  Returns the two registers to compare.
-/
def icmpCastExtP (regType : Puddle.Handle OpCode .type) (lhs rhs : Puddle.Handle OpCode .value)
    (ext : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp))) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value × Puddle.Handle OpCode .value) := do
  let lhsReg ← createCastP lhs regType
  let rhsReg ← createCastP rhs regType
  match ext with
  | none => return (lhsReg, rhsReg)
  | some ⟨extOp, extProps'⟩ =>
    let extProps ← Puddle.CreateProg.property (.riscv extOp) extProps'
    let lhsExt ← createRiscvWithP extOp extProps #[lhsReg] regType
    let rhsExt ← createRiscvWithP extOp extProps #[rhsReg] regType
    return (lhsExt, rhsExt)

/--
  The comparison sequence of the `icmp` arm for `pred` on the comparison registers `a` and `b`.
  `zeroRhs` selects the `eq`/`ne`-against-zero peepholes, which compare the left register
  directly (`seqz`/`snez`) instead of the `xor` of both.
-/
def icmpEmitP (regType : Puddle.Handle OpCode .type) (pred : Data.LLVM.IntPred) (zeroRhs : Bool)
    (a b : Puddle.Handle OpCode .value) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value) :=
  match pred, zeroRhs with
  /- `seqz`: `sltiu a 1`. -/
  | .eq, true => createRiscvP .sltiu icmpOneImm #[a] regType
  /- `sltiu (xor b a) 1`. -/
  | .eq, false => do
    let diff ← createRiscvP .xor () #[b, a] regType
    createRiscvP .sltiu icmpOneImm #[diff] regType
  /- `snez`: `sltu 0 a`. The `riscv.li 0` becomes `x0` under `riscv-combine` (see
     `li_zero_to_x0`). -/
  | .ne, true => do
    let zero ← createRiscvP .li icmpZeroImm #[] regType
    createRiscvP .sltu () #[zero, a] regType
  /- `sltu 0 (xor b a)`. -/
  | .ne, false => do
    let diff ← createRiscvP .xor () #[b, a] regType
    let zero ← createRiscvP .li icmpZeroImm #[] regType
    createRiscvP .sltu () #[zero, diff] regType
  | .slt, _ => createRiscvP .slt () #[a, b] regType
  | .sgt, _ => createRiscvP .slt () #[b, a] regType
  | .ult, _ => createRiscvP .sltu () #[a, b] regType
  | .ugt, _ => createRiscvP .sltu () #[b, a] regType
  | .sge, _ => do
    let cmp ← createRiscvP .slt () #[a, b] regType
    createRiscvP .xori icmpOneImm #[cmp] regType
  | .sle, _ => do
    let cmp ← createRiscvP .slt () #[b, a] regType
    createRiscvP .xori icmpOneImm #[cmp] regType
  | .uge, _ => do
    let cmp ← createRiscvP .sltu () #[a, b] regType
    createRiscvP .xori icmpOneImm #[cmp] regType
  | .ule, _ => do
    let cmp ← createRiscvP .sltu () #[b, a] regType
    createRiscvP .xori icmpOneImm #[cmp] regType

/--
  `llvm.icmp pred` whose lhs is `lhsWidth` bits wide in a register (`i64`/`!llvm.ptr`, `i32`, or
  `i8`). When `zeroRhs` is set, the rhs must be a constant `0` (the `eq`/`ne` peepholes).
-/
def lowerIcmp (pred : Data.LLVM.IntPred) (lhsWidth : Nat) (zeroRhs : Bool) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let lhsType ← Puddle.MatchProg.type (Attr := TypeAttr)
        (fun t => icmpTypeWidth? t == some lhsWidth)
      let lhs ← Puddle.MatchProg.value lhsType
      let (rhs, rhsType) ← if zeroRhs then matchConstantZeroP else do
        let rhsType ← Puddle.MatchProg.type (Attr := TypeAttr)
        pure (← Puddle.MatchProg.value rhsType, rhsType)
      /- support `i64`, `i32`, `i8` and `!llvm.ptr` -/
      Puddle.MatchProg.matchNative rhsType fun t => (icmpTypeWidth? t).any (· ∈ [64, 32, 8])
      /- The result is cast back for type consistency, so it must be an integer type. -/
      let resType ← Puddle.MatchProg.type (Attr := IntegerType)
      let _ ← Puddle.MatchProg.root (.llvm .icmp) #[lhs, rhs] #[resType]
        (fun props => props.predicate == pred)
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let (a, b) ← icmpCastExtP regType lhs rhs (icmpExtOf lhsWidth)
      let res ← icmpEmitP regType pred zeroRhs a b
      createCastP res resType)
    (fun res => res)

/--
  llvm.icmp -> riscv comparison sequence (see the arms above).

  The `eq`/`ne` peepholes against a constant-`0` rhs come first, so they take priority over the
  generic arms. Canonicalization runs before isel and moves the constant to the rhs, so we only
  check that side.
  LLVM: `Pat<(riscv_seteq GPR:$rs1), (SLTIU GPR:$rs1, 1)>` and
  `Pat<(riscv_setne GPR:$rs1), (SLTU (XLenVT X0), GPR:$rs1)>`.
  https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1649
-/
def icmpPatterns : Array (Puddle.CompiledPattern OpCode) :=
  let widths := #[64, 32, 8]
  let preds : Array Data.LLVM.IntPred :=
    #[.eq, .ne, .slt, .sgt, .ult, .ugt, .sge, .sle, .uge, .ule]
  let peepholes := widths.flatMap fun w => #[.eq, .ne].map fun pred => lowerIcmp pred w true
  let generic := widths.flatMap fun w => preds.map fun pred => lowerIcmp pred w false
  (peepholes ++ generic).map (·.compile)

/-- llvm.or -> riscv.or (bitwise, so one instruction for every legal width) -/
def or : Puddle.CompiledPattern OpCode := or_pattern.compile

/-- llvm.xor -> riscv.xor -/
def xor64 : Puddle.CompiledPattern OpCode := xor64_pattern.compile

/-- llvm.xor -> riscv.xor (no `W` variant needed: xor is bitwise) -/
def xor32 : Puddle.CompiledPattern OpCode := xor32_pattern.compile

/-- llvm.mul -> riscv.mul -/
def mul64 : Puddle.CompiledPattern OpCode := mul64_pattern.compile

/-- llvm.mul -> riscv.mulw (sign-extends the result) -/
def mul32 : Puddle.CompiledPattern OpCode := mul32_pattern.compile

/-- llvm.sdiv -> riscv.div -/
def sdiv64 : Puddle.CompiledPattern OpCode := sdiv64_pattern.compile

/-- llvm.sdiv -> riscv.divw -/
def sdiv32 : Puddle.CompiledPattern OpCode := sdiv32_pattern.compile

/-- llvm.udiv -> riscv.divu -/
def udiv64 : Puddle.CompiledPattern OpCode := udiv64_pattern.compile

/-- llvm.udiv -> riscv.divuw -/
def udiv32 : Puddle.CompiledPattern OpCode := udiv32_pattern.compile

/-- llvm.srem -> riscv.rem -/
def srem64 : Puddle.CompiledPattern OpCode := srem64_pattern.compile

/-- llvm.srem -> riscv.remw -/
def srem32 : Puddle.CompiledPattern OpCode := srem32_pattern.compile

/-- llvm.urem -> riscv.remu -/
def urem64 : Puddle.CompiledPattern OpCode := urem64_pattern.compile

/-- llvm.urem -> riscv.remuw -/
def urem32 : Puddle.CompiledPattern OpCode := urem32_pattern.compile

/-- llvm.sub -> riscv.sub -/
def sub64 : Puddle.CompiledPattern OpCode := sub64_pattern.compile

/-- llvm.sub -> riscv.subw -/
def sub32 : Puddle.CompiledPattern OpCode := sub32_pattern.compile

/--
  llvm.sext %x `i8`  to `i32` -> riscv.sextb %x
  llvm.sext %x `i8`  to `i64` -> riscv.sextb %x
  llvm.sext %x `i16` to `i64` -> riscv.sexth %x
  llvm.sext %x `i16` to `i32` -> riscv.sexth %x
  llvm.sext %x `i32` to `i64` -> riscv.sextw %x
-/
def sext8 : Puddle.CompiledPattern OpCode := sext8_pattern.compile

def sext16 : Puddle.CompiledPattern OpCode := sext16_pattern.compile

def sext32 : Puddle.CompiledPattern OpCode := sext32_pattern.compile
/--
  llvm.zext %x `i8`  to `i32` -> riscv.zextb %x
  llvm.zext %x `i8`  to `i64` -> riscv.zextb %x
  llvm.zext %x `i16` to `i64` -> riscv.zexth %x
  llvm.zext %x `i16` to `i32` -> riscv.zexth %x
  llvm.zext %x `i32` to `i64` -> riscv.zextw %x
-/
def zext8 : Puddle.CompiledPattern OpCode := zext8_pattern.compile

def zext16 : Puddle.CompiledPattern OpCode := zext16_pattern.compile

def zext32 : Puddle.CompiledPattern OpCode := zext32_pattern.compile

/--
  Whether `llvm.trunc` from `opType` to `resType` is lowered: both are integer types or both are
  byte types, and the result is strictly narrower.

  The operand is held in a 64-bit register, so an operand wider than 64 bits would lose bits in
  the round trip. Every narrower pair of widths is sound (see `trunc_refinement_le64`), including
  odd ones such as `i1`: the result's upper register bits are whatever the operand left there,
  and `reconcile-cast` zero-extends the value wherever it is used as a register again.
-/
def isLegalTrunc (opType resType : TypeAttr) : Bool :=
  let sameKind := match opType.val, resType.val with
    | .integerType _, .integerType _ => true
    | .byteType _, .byteType _ => true
    | _, _ => false
  match getIntByteTypeBitwidth opType, getIntByteTypeBitwidth resType with
  | some opBw, some resBw => sameKind && resBw < opBw && opBw ≤ 64
  | _, _ => false

/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!riscv.reg) : iY
  where `iY`'s width is smaller than `iX`'s (see `isLegalTrunc`).
  Also accepts the byte type.
-/
def trunc : Puddle.CompiledPattern OpCode := (lowerRegCast .trunc isLegalTrunc).compile

/--
  Shared shape of the binary RISC-V lowerings that accept both integer and byte values
  (`shl`/`lshr`), for operands of width `bw`.
-/
def lowerShift (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Puddle.Pattern OpCode :=
  lowerOpP llvmOp 2 (fun t => getIntByteTypeBitwidth t == some bw) fun regType operands => do
    let lhs ← createCastP operands[0]! regType
    let rhs ← createCastP operands[1]! regType
    createRiscvP riscvOp riscvProps #[lhs, rhs] regType

/-- llvm.shl -> riscv.sll -/
def shl64 : Puddle.CompiledPattern OpCode := (lowerShift .shl 64 .sll ()).compile

/-- llvm.shl -> riscv.sllw -/
def shl32 : Puddle.CompiledPattern OpCode := (lowerShift .shl 32 .sllw ()).compile

/-- llvm.lshr -> riscv.srl -/
def lshr64 : Puddle.CompiledPattern OpCode := (lowerShift .lshr 64 .srl ()).compile

/-- llvm.lshr -> riscv.srlw -/
def lshr32 : Puddle.CompiledPattern OpCode := (lowerShift .lshr 32 .srlw ()).compile

def checkBitcastType (t : TypeAttr) : Bool :=
  match t.val with
  | .llvmPointerType _
  | .integerType _
  | .byteType _ => true
  | _ => false

/-- Is this a `byte -> ptr` bitcast? -/
def isBitcastByteToPtr (opType resType : TypeAttr) : Bool :=
  match opType.val, resType.val with
  | .byteType _, .llvmPointerType _ => true
  | _, _ => false

/-- Whether `llvm.bitcast` from `opType` to `resType` is lowered (see `bitcast`). -/
def isLegalBitcast (opType resType : TypeAttr) : Bool :=
  checkBitcastType opType && checkBitcastType resType && !isBitcastByteToPtr opType resType &&
    match Attribute.bitwidthOfType opType, Attribute.bitwidthOfType resType with
    | some opBw, some resBw => opBw ∈ [8, 16, 32, 64] && resBw ∈ [8, 16, 32, 64]
    | _, _ => false

/--
  llvm.bitcast t1 %x to t2 -> builtin_unrealized_conversion_cast
  Integers, bytes, and pointers are all lowered to !riscv.reg, making this basically a no-op.
  The `byte -> ptr` case is excluded.
-/
def bitcast : Puddle.CompiledPattern OpCode := (lowerRegCast .bitcast isLegalBitcast).compile

/--
  Lower LLVM lifetime instructions to nothing. This is a refinement that we can
  revisit later if we want to perform certain stack slot optimizations.
-/
def lowerLifetime (llvmOp : Llvm) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let ptrType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let ptr ← Puddle.MatchProg.value ptrType
      let _ ← Puddle.MatchProg.root (.llvm llvmOp) #[ptr] #[]
      return ())
    pure
    (fun () => ⟨#[]⟩)

/-- Erase `llvm.intr.lifetime.start`. -/
def lifetimeStart : Puddle.CompiledPattern OpCode := (lowerLifetime .intr__lifetime__start).compile

/-- Erase `llvm.intr.lifetime.end`. -/
def lifetimeEnd : Puddle.CompiledPattern OpCode := (lowerLifetime .intr__lifetime__end).compile

/--
  Lower a constant-count entry-block allocation to a fixed RISC-V stack object.
  Dynamic allocations and `inalloca` need additional stack-lifetime support in the backend.
  Run before constant selection so the count still has an integer runtime value.
-/
def alloca_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operands, properties) := matchOp op ctx.raw Llvm.alloca 1 | return (ctx, none)
  if properties.inalloca then return (ctx, none)
  let .llvmPointerType _ := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  let some parentOp := op.getParentOp! ctx.raw | return (ctx, none)
  let some funcOp := FunctionOp.of? parentOp ctx.raw | return (ctx, none)
  let some entry := funcOp.getEntryBlock? | return (ctx, none)
  if (op.get! ctx.raw).parent != some entry then return (ctx, none)
  let some (.int _ (.val count)) := operands[0]!.constantValue ctx.raw | return (ctx, none)
  let some layout := DataLayout.riscv64.query properties.elem_type.val | return (ctx, none)
  let size := count.toNat * layout.allocSize
  /- Do not silently wrap the fixed object's size to a signed 64-bit value. -/
  if size >= 2 ^ 63 then return (ctx, none)
  let alignment : Int := if properties.alignment.value = 0 then layout.abiAlignment
    else properties.alignment.value
  if !isValidLLVMAlignment alignment || alignment >= 2 ^ 63 then
    return (ctx, none)
  let props : RISCVStackAllocaProperties :=
    { size := BitVec.ofNat 64 size
      alignment := BitVec.ofInt 64 alignment }
  let (ctx, stackOp) ← WfRewriter.createOp! ctx Riscv_Stack.alloca #[RegisterType.mk]
      #[] #[] #[] props none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (stackOp.getResult 0)
  some (ctx, some (#[stackOp, castBackOp], #[castBackOp.getResult 0]))

/-- `llvm.alloca` -> `riscv_stack.alloca` and a cast back to the pointer type. -/
def alloca (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite alloca_local rewriter op opInBounds

/-- Resolve a global in the nearest enclosing module, without entering nested modules. -/
private partial def lookupGlobal? (ctx : IRContext OpCode) (op : OperationPtr)
    (name : ByteArray) : Option LLVMGlobalProperties := do
  let parent ← op.getParentOp! ctx
  if parent.getOpType! ctx != .builtin .module then
    return ← lookupGlobal? ctx parent name
  let body := parent.getRegion! ctx 0
  let block ← (body.get! ctx).firstBlock
  let mut candidate := (block.get! ctx).firstOp
  while let some target := candidate do
    if target.getOpType! ctx == .llvm .mlir__global then
      let props := target.getProperties! ctx Llvm.mlir__global
      if props.sym_name.value == name then return props
    candidate := (target.get! ctx).next
  none

/-- `llvm.mlir.addressof` -> `riscv.la`, except for TLS and external weak globals. -/
def addressof_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (_, properties) := matchOp op ctx.raw Llvm.mlir__addressof 0 | return (ctx, none)
  let some name := properties.global_name.getName? | return (ctx, none)
  if let some global := lookupGlobal? ctx.raw op name then
    -- An undefined weak symbol resolves to zero, which a PC-relative `la`
    -- cannot always reach. Leave it until GOT-based address lowering is supported.
    if global.isThreadLocal || global.linkage.value == "extern_weak" then return (ctx, none)
  let (ctx, laOp) ← WfRewriter.createOp! ctx Riscv.la #[RegisterType.mk]
      #[] #[] #[] (RISCVSymbolProperties.mk properties.global_name) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (laOp.getResult 0)
  some (ctx, some (#[laOp, castBackOp], #[castBackOp.getResult 0]))

/-- `llvm.mlir.addressof` -> `riscv.la` and a cast back to the pointer type. -/
def addressof (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite addressof_local rewriter op opInBounds

/-- The width in bytes of a load or store of a value of `type`, for the integers
  and pointers whose data-layout size fits one `l*`/`s*` instruction. An integer
  must fill its bytes exactly, since `getTypeSize` rounds an odd width up. -/
def memAccessWidth? (type : TypeAttr) : Option Nat := do
  match type.val with
  | .integerType t => guard (t.bitwidth % 8 = 0)
  | .llvmPointerType _ => pure ()
  | _ => none
  let width ← DataLayout.riscv64.getTypeSize type.val
  guard (width ∈ [1, 2, 4, 8])
  return width

/-- `riscv.lb` / `riscv.lh` / `riscv.lw` / `riscv.ld`, for a `width`-byte load. -/
def createLoadLocal (ctx : WfIRContext OpCode) (width : Nat) (addr : ValuePtr)
    (props : RISCVMemProperties) : Option (WfIRContext OpCode × OperationPtr) :=
  match width with
  | 1 => WfRewriter.createOp! ctx Riscv.lb #[RegisterType.mk] #[addr] #[] #[] props none
  | 2 => WfRewriter.createOp! ctx Riscv.lh #[RegisterType.mk] #[addr] #[] #[] props none
  | 4 => WfRewriter.createOp! ctx Riscv.lw #[RegisterType.mk] #[addr] #[] #[] props none
  | _ => WfRewriter.createOp! ctx Riscv.ld #[RegisterType.mk] #[addr] #[] #[] props none

/-- `riscv.sb` / `riscv.sh` / `riscv.sw` / `riscv.sd`, for a `width`-byte store. -/
def createStoreLocal (ctx : WfIRContext OpCode) (width : Nat) (val addr : ValuePtr)
    (props : RISCVMemProperties) : Option (WfIRContext OpCode × OperationPtr) :=
  match width with
  | 1 => WfRewriter.createOp! ctx Riscv.sb #[] #[val, addr] #[] #[] props none
  | 2 => WfRewriter.createOp! ctx Riscv.sh #[] #[val, addr] #[] #[] props none
  | 4 => WfRewriter.createOp! ctx Riscv.sw #[] #[val, addr] #[] #[] props none
  | _ => WfRewriter.createOp! ctx Riscv.sd #[] #[val, addr] #[] #[] props none

/--
  The allocation size (ABI stride) of the element type of a single-dynamic-index
  `llvm.getelementptr` with properties `gep`: the factor its index is scaled by. `none` if the
  `getelementptr` has trailing constant indices or the element type has no known size.
-/
def gepScale? (gep : GetelementptrProperties) : Option Nat := do
  guard (gep.rawConstantIndices.values = #[(-2147483648 : Int)])
  DataLayout.riscv64.getTypeAllocSize gep.elem_type.val

/--
  The offset that a single-dynamic-index `llvm.getelementptr` with properties `gep` and a
  constant `i64` index (of type `idxType` and properties `idx`) adds to its base, when it fits a
  load/store's signed 12-bit immediate. This mirrors the `isBaseWithConstantOffset` case of LLVM's
  [`RISCVDAGToDAGISel::SelectAddrRegImm`](https://github.com/llvm/llvm-project/blob/llvmorg-22.1.8/llvm/lib/Target/RISCV/RISCVISelDAGToDAG.cpp#L3175-L3206).
-/
def gepFoldedOffset? (idxType : TypeAttr) (gep : GetelementptrProperties)
    (idx : LLVMConstantProperties) : Option Int := do
  let scale ← gepScale? gep
  let c ← constIntValue? idxType idx
  let offset := c * (scale : Int)
  guard (-2048 ≤ offset ∧ offset ≤ 2047)
  return offset

/-- The index type, `getelementptr` properties, and index-constant properties of an address
    `getelementptr base, c` folded into a load/store's immediate offset. -/
abbrev FoldedAddrHandles :=
  Puddle.Handle OpCode .type × Puddle.Handle OpCode (.prop (.llvm .getelementptr)) ×
    Puddle.Handle OpCode (.prop (.llvm .mlir__constant))

/--
  Puddle match step: the address of a load/store, split into a base register operand and a signed
  12-bit immediate offset. When `folded` is set, the address must be a `getelementptr base, c`
  whose constant offset folds into the immediate (see `gepFoldedOffset?`); otherwise the address
  is the base itself at offset `0`. Returns the address, the base, and the metadata of the folded
  `getelementptr` if any.
-/
def matchAddrRegImmP (folded : Bool) :
    Puddle.MatchProg.Builder (Puddle.Handle OpCode .value × Puddle.Handle OpCode .value ×
      Option FoldedAddrHandles) := do
  let baseType ← Puddle.MatchProg.type (Attr := TypeAttr)
  let base ← Puddle.MatchProg.value baseType
  if folded then
    let (idx, idxType, idxProps) ← matchConstantIntP (·.bitwidth == 64)
    let addrType ← Puddle.MatchProg.type (Attr := TypeAttr)
    let gep ← Puddle.MatchProg.operation (.llvm .getelementptr) #[base, idx] #[addrType]
    Puddle.MatchProg.matchNative (idxType, gep.properties, idxProps)
      fun (idxType, gep, idx) => (gepFoldedOffset? idxType gep idx).isSome
    return (gep.res[0]!, base, some (idxType, gep.properties, idxProps))
  else
    return (base, base, none)

/-- Puddle creation step: the immediate offset of an address matched by `matchAddrRegImmP`. -/
def createAddrOffsetP : Option FoldedAddrHandles →
    Puddle.CreateProg.Builder (Puddle.Handle OpCode (.prop (.riscv .li)))
  | none => Puddle.CreateProg.property (.riscv .li) (mkRISCVImm 0)
  | some folded =>
    Puddle.CreateProg.applyNative (Outputs := Puddle.Handle OpCode (.prop (.riscv .li))) folded
      fun (idxType, gep, idx) => (gepFoldedOffset? idxType gep idx).map mkRISCVImm

/--
  llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8), for a
  `width`-byte load.
-/
def lowerLoad (folded : Bool) (width : Nat) (riscvOp : Riscv)
    (h : propertiesOf (OpCode.riscv riscvOp) = RISCVMemProperties := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let (addr, base, folded) ← matchAddrRegImmP folded
      /- support `i64`, `i32`, `i16`, `i8` and `!llvm.ptr` (the loaded value type) -/
      let resType ← Puddle.MatchProg.type (Attr := TypeAttr) (memAccessWidth? · == some width)
      let root ← Puddle.MatchProg.root (.llvm .load) #[addr] #[resType]
      return (resType, base, folded, root.properties))
    (fun (resType, base, folded, loadProps) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      /- cast base (!llvm.ptr) -> register -/
      let baseReg ← createCastP base regType
      /- Volatility carries over from the `llvm.load`: the riscv op encodes the same, but the
         flag keeps later passes from deleting or duplicating the access. -/
      let offset ← createAddrOffsetP folded
      let memProps ← Puddle.CreateProg.applyNative
        (Outputs := Puddle.Handle OpCode (.prop (.riscv riscvOp))) (offset, loadProps)
        fun (offset, loadProps) =>
          some (cast h.symm (RISCVMemProperties.mk offset.value loadProps.volatile_))
      let ld ← createRiscvWithP riscvOp memProps #[baseReg] regType
      createCastP ld resType)
    (fun res => res)

/--
  llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8), for a
  `width`-byte store.
-/
def lowerStore (folded : Bool) (width : Nat) (riscvOp : Riscv)
    (h : propertiesOf (OpCode.riscv riscvOp) = RISCVMemProperties := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      /- support `i64`, `i32`, `i16`, `i8` and `!llvm.ptr` (the stored value type) -/
      let valType ← Puddle.MatchProg.type (Attr := TypeAttr) (memAccessWidth? · == some width)
      let val ← Puddle.MatchProg.value valType
      let (addr, base, folded) ← matchAddrRegImmP folded
      let root ← Puddle.MatchProg.root (.llvm .store) #[val, addr] #[]
      return (val, base, folded, root.properties))
    (fun (val, base, folded, storeProps) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      /- cast base (!llvm.ptr) -> register -/
      let baseReg ← createCastP base regType
      /- cast value (i64/i32/i16/i8/ptr) -> register -/
      let valReg ← createCastP val regType
      /- The store writes the low `width` bytes of the value register. Volatility carries over
         from the `llvm.store`, as in `lowerLoad`. -/
      let offset ← createAddrOffsetP folded
      let memProps ← Puddle.CreateProg.applyNative
        (Outputs := Puddle.Handle OpCode (.prop (.riscv riscvOp))) (offset, storeProps)
        fun (offset, storeProps) =>
          some (cast h.symm (RISCVMemProperties.mk offset.value storeProps.volatile_))
      let _ ← Puddle.CreateProg.operation (.riscv riscvOp) #[valReg, baseReg] #[] memProps
      return ())
    (fun () => ⟨#[]⟩)

/--
  llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8).
  The patterns folding a constant `getelementptr` offset into the immediate come first.
-/
def loadPatterns : Array (Puddle.CompiledPattern OpCode) :=
  #[true, false].flatMap fun folded =>
    #[lowerLoad folded 1 .lb, lowerLoad folded 2 .lh, lowerLoad folded 4 .lw,
      lowerLoad folded 8 .ld].map (·.compile)

/--
  llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8).
  The patterns folding a constant `getelementptr` offset into the immediate come first.
-/
def storePatterns : Array (Puddle.CompiledPattern OpCode) :=
  #[true, false].flatMap fun folded =>
    #[lowerStore folded 1 .sb, lowerStore folded 2 .sh, lowerStore folded 4 .sw,
      lowerStore folded 8 .sd].map (·.compile)

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`, where `scale`
  is the allocation size (ABI stride) of the element type and is accepted by `accepts`. `emit`
  computes the address from the pointer and index registers.
-/
def lowerGetelementptr (accepts : Nat → Bool)
    (emit : Puddle.Handle OpCode .type → Puddle.Handle OpCode .value →
      Puddle.Handle OpCode .value → Puddle.Handle OpCode (.prop (.llvm .getelementptr)) →
      Puddle.CreateProg.Builder (Puddle.Handle OpCode .value)) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let ptrType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let ptr ← Puddle.MatchProg.value ptrType
      /- The index must be `i64`. -/
      let idxType ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth == 64)
      let idx ← Puddle.MatchProg.value idxType
      let resType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let root ← Puddle.MatchProg.root (.llvm .getelementptr) #[ptr, idx] #[resType]
      Puddle.MatchProg.matchNative root.properties fun gep => (gepScale? gep).any accepts
      return (resType, ptr, idx, root.properties))
    (fun (resType, ptr, idx, gep) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let ptrReg ← createCastP ptr regType
      let idxReg ← createCastP idx regType
      let res ← emit regType ptrReg idxReg gep
      /- Cast the resulting register back to `!llvm.ptr`. -/
      createCastP res resType)
    (fun res => res)

/--
  Whether a `getelementptr` scale is a power of two handled by a single `slli`. `0 < scale`
  excludes zero-sized element types (`i0`, `!llvm.array<0 x _>`), for which
  `scale &&& (scale - 1) == 0` also holds but `Nat.log2 0 = 0` would emit `idx << 0`, i.e.
  `ptr + idx` rather than `ptr`. `Nat.log2 scale < 64` excludes element sizes of `2^64` and
  beyond, whose shift amount does not fit the 6-bit immediate. Both fall through to the
  `li`/`mul` form, which truncates modulo `2^64` exactly as the source does.
-/
def isGepShiftScale (scale : Nat) : Bool :=
  0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the allocation size (ABI stride) of the element type.
-/
def getelementptrPatterns : Array (Puddle.CompiledPattern OpCode) := #[
  /- ptr + idx -/
  lowerGetelementptr (· == 1) fun regType ptr idx _ =>
    createRiscvP .add () #[ptr, idx] regType,
  /- (idx << 1) + ptr -/
  lowerGetelementptr (· == 2) fun regType ptr idx _ =>
    createRiscvP .sh1add () #[idx, ptr] regType,
  /- (idx << 2) + ptr -/
  lowerGetelementptr (· == 4) fun regType ptr idx _ =>
    createRiscvP .sh2add () #[idx, ptr] regType,
  /- (idx << 3) + ptr -/
  lowerGetelementptr (· == 8) fun regType ptr idx _ =>
    createRiscvP .sh3add () #[idx, ptr] regType,
  /- scale is a power of two: ptr + (idx << log2 scale) -/
  lowerGetelementptr (fun s => s ∉ [1, 2, 4, 8] ∧ isGepShiftScale s) fun regType ptr idx gep => do
    let shamt ← Puddle.CreateProg.applyNative
      (Outputs := Puddle.Handle OpCode (.prop (.riscv .slli))) gep
      fun gep => (gepScale? gep).map fun scale => mkRISCVImm (Nat.log2 scale)
    let shifted ← createRiscvWithP .slli shamt #[idx] regType
    createRiscvP .add () #[ptr, shifted] regType,
  /- arbitrary scale: ptr + idx * scale -/
  lowerGetelementptr (fun s => s ∉ [1, 2, 4, 8] ∧ !isGepShiftScale s) fun regType ptr idx gep => do
    let scaleImm ← Puddle.CreateProg.applyNative
      (Outputs := Puddle.Handle OpCode (.prop (.riscv .li))) gep
      fun gep => (gepScale? gep).map fun scale => mkRISCVImm scale
    let scale ← createRiscvWithP .li scaleImm #[] regType
    let scaled ← createRiscvP .mul () #[idx, scale] regType
    createRiscvP .add () #[ptr, scaled] regType
].map (·.compile)

/-! ## Zicond branchless `select` lowering

  The Zicond extension lowers `llvm.select` branchlessly (mirroring LLVM's
  SelectionDAG lowering of `ISD::SELECT` when `Zicond` is available):
  ```
    (select c, t, 0) -> (czero.eqz t, c)
    (select c, 0, f) -> (czero.nez f, c)
    (select c, t, f) -> (or (czero.eqz t, c), (czero.nez f, c))
  ```
  The single-instruction zero-arm cases take priority over the general form;
  the greedy driver tries patterns in array order, so `selectCzeroeqz` and
  `selectCzeronez` are registered before `selectGeneral`.
-/

/--
  `select c t 0` -> `riscv.czeroeqz t c` (`zeroTrue` unset), or
  `select c 0 f` -> `riscv.czeronez f c` (`zeroTrue` set).
-/
def lowerSelectCzero (zeroTrue : Bool) : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let condType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let cond ← Puddle.MatchProg.value condType
      let valType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let val ← Puddle.MatchProg.value valType
      let (zero, _) ← matchConstantZeroP
      let resType ← Puddle.MatchProg.type (Attr := IntegerType)
        (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32)
      let operands := if zeroTrue then #[cond, zero, val] else #[cond, val, zero]
      let _ ← Puddle.MatchProg.root (.llvm .select) operands #[resType]
      return (resType, cond, val))
    (fun (resType, cond, val) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let valReg ← createCastP val regType
      let condReg ← createCastP cond regType
      let res ← if zeroTrue then
          createRiscvP .czeronez () #[valReg, condReg] regType
        else
          createRiscvP .czeroeqz () #[valReg, condReg] regType
      createCastP res resType)
    (fun res => res)

/--
  `select c t 0` -> `riscv.czeroeqz t c`.
-/
def selectCzeroeqz : Puddle.CompiledPattern OpCode := (lowerSelectCzero false).compile

/--
  `select c 0 f` -> `riscv.czeronez f c`.
-/
def selectCzeronez : Puddle.CompiledPattern OpCode := (lowerSelectCzero true).compile

/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral_pattern : Puddle.Pattern OpCode :=
  lowerOpP .select 3 (isIntTypeOfWidth [64, 32, 1]) fun regType operands => do
    let tReg ← createCastP operands[1]! regType
    let fReg ← createCastP operands[2]! regType
    let condReg ← createCastP operands[0]! regType
    let eqz ← createRiscvP .czeroeqz () #[tReg, condReg] regType
    let nez ← createRiscvP .czeronez () #[fReg, condReg] regType
    createRiscvP .or () #[eqz, nez] regType

/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral : Puddle.CompiledPattern OpCode := selectGeneral_pattern.compile

/-! ## Zbb min/max and rotate intrinsics

  These mirror the simple one-to-one patterns in LLVM's RISC-V backend
  (`RISCVInstrInfoZb.td`): `smin/smax/umin/umax` select to `MIN/MAX/MINU/MAXU`,
  and a funnel shift whose two data operands are identical is a rotate, which
  selects to `ROL`/`ROR`. The general (distinct-operand) funnel shift needs a
  multi-instruction expansion and is intentionally left unselected.
-/

/-- llvm.intr.smax -> riscv.max -/
def smax64 : Puddle.CompiledPattern OpCode := smax64_pattern.compile

def smax32 : Puddle.CompiledPattern OpCode := smax32_pattern.compile

/-- llvm.intr.smin -> riscv.min -/
def smin64 : Puddle.CompiledPattern OpCode := smin64_pattern.compile

def smin32 : Puddle.CompiledPattern OpCode := smin32_pattern.compile

/-- llvm.intr.umax -> riscv.maxu -/
def umax : Puddle.CompiledPattern OpCode := umax_pattern.compile

/-- llvm.intr.umin -> riscv.minu -/
def umin : Puddle.CompiledPattern OpCode := umin_pattern.compile

/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol (riscv.rolw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl64 : Puddle.CompiledPattern OpCode := fshl64_pattern.compile

def fshl32 : Puddle.CompiledPattern OpCode := fshl32_pattern.compile

/-! ## Saturating integer intrinsics

  These mirror LLVM's RV64+Zbb+Zicond lowering for scalar i64 saturating
  arithmetic. The signed cases compute the wrapped result and an overflow
  predicate, build the signed saturation endpoint, then select with Zicond:

    `or (czero.eqz saturated overflow) (czero.nez wrapped overflow)`

  Unsigned add/sub use the compact Zbb min/max idioms selected by LLVM.

  The generic DAG expansions live in
  `llvm/lib/CodeGen/SelectionDAG/TargetLowering.cpp`:
    * `TargetLowering::expandAddSubSat`  (add/sub sat)      @ line 12432
    * `TargetLowering::expandShlSat`     (shl sat)          @ line 12598
    * `TargetLowering::expandSADDSUBO`   (signed overflow)  @ line 13046
  The signed `select`s become Zicond `czero.{eqz,nez}`/`or`, and the signed
  saturation constant `select(x<0, INT_MIN, INT_MAX)` folds to `(x >>s 63) ^
  INT_MAX`. Each sequence below was confirmed identical, instruction for
  instruction, to `llc -mtriple=riscv64 -mattr=+zbb,+zicond`
  (LLVM commit d9906882fc61).
-/

def createRISCVImmLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (operands : Array ValuePtr) (value : Int) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm (mkRISCVImm value)) none

def createRISCVUnitLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = Unit) (operands : Array ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx dst #[RegisterType.mk] operands #[] #[]
      (cast h.symm ()) none

/-- The Zicond select `or (czero.eqz sat overflow) (czero.nez wrapped overflow)`. -/
def signedSatSelectP (regType : Puddle.Handle OpCode .type)
    (wrapped overflow sat : Puddle.Handle OpCode .value) :
    Puddle.CreateProg.Builder (Puddle.Handle OpCode .value) := do
  let wrappedOrZero ← createRiscvP .czeronez () #[wrapped, overflow] regType
  let satOrZero ← createRiscvP .czeroeqz () #[sat, overflow] regType
  createRiscvP .or () #[satOrZero, wrappedOrZero] regType

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__sadd__sat 2 (isIntTypeOfWidth [64]) fun regType operands => do
    let lReg ← createCastP operands[0]! regType
    let rReg ← createCastP operands[1]! regType
    let minusOne ← createRiscvP .li (mkRISCVImm (-1)) #[] regType
    let sum ← createRiscvP .add () #[lReg, rReg] regType
    let rhsSign ← createRiscvP .srli (mkRISCVImm 63) #[rReg] regType
    let carryLike ← createRiscvP .slt () #[sum, lReg] regType
    let sumSign ← createRiscvP .srai (mkRISCVImm 63) #[sum] regType
    let intMin ← createRiscvP .slli (mkRISCVImm 63) #[minusOne] regType
    let overflow ← createRiscvP .xor () #[rhsSign, carryLike] regType
    let sat ← createRiscvP .xor () #[sumSign, intMin] regType
    signedSatSelectP regType sum overflow sat

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence
    (see `saddSat_pattern`). -/
def saddSat : Puddle.CompiledPattern OpCode := saddSat_pattern.compile

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__ssub__sat 2 (isIntTypeOfWidth [64]) fun regType operands => do
    let lReg ← createCastP operands[0]! regType
    let rReg ← createCastP operands[1]! regType
    let minusOne ← createRiscvP .li (mkRISCVImm (-1)) #[] regType
    let diff ← createRiscvP .sub () #[lReg, rReg] regType
    let cmp ← createRiscvP .slt () #[lReg, rReg] regType
    let diffSignBit ← createRiscvP .srli (mkRISCVImm 63) #[diff] regType
    let diffSign ← createRiscvP .srai (mkRISCVImm 63) #[diff] regType
    let intMin ← createRiscvP .slli (mkRISCVImm 63) #[minusOne] regType
    let overflow ← createRiscvP .xor () #[cmp, diffSignBit] regType
    let sat ← createRiscvP .xor () #[diffSign, intMin] regType
    signedSatSelectP regType diff overflow sat

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence
    (see `ssubSat_pattern`). -/
def ssubSat : Puddle.CompiledPattern OpCode := ssubSat_pattern.compile

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__uadd__sat 2 (isIntTypeOfWidth [64]) fun regType operands => do
    let lReg ← createCastP operands[0]! regType
    let rReg ← createCastP operands[1]! regType
    let notRhs ← createRiscvP .xori (mkRISCVImm (-1)) #[rReg] regType
    let minu ← createRiscvP .minu () #[lReg, notRhs] regType
    createRiscvP .add () #[minu, rReg] regType

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs (see `uaddSat_pattern`). -/
def uaddSat : Puddle.CompiledPattern OpCode := uaddSat_pattern.compile

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__usub__sat 2 (isIntTypeOfWidth [64]) fun regType operands => do
    let lReg ← createCastP operands[0]! regType
    let rReg ← createCastP operands[1]! regType
    let maxu ← createRiscvP .maxu () #[lReg, rReg] regType
    createRiscvP .sub () #[maxu, rReg] regType

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs (see `usubSat_pattern`). -/
def usubSat : Puddle.CompiledPattern OpCode := usubSat_pattern.compile

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__sshl__sat 2 (isIntTypeOfWidth [64]) fun regType operands => do
    let lReg ← createCastP operands[0]! regType
    let rReg ← createCastP operands[1]! regType
    let shifted ← createRiscvP .sll () #[lReg, rReg] regType
    let minusOne ← createRiscvP .li (mkRISCVImm (-1)) #[] regType
    let unshifted ← createRiscvP .sra () #[shifted, rReg] regType
    let sign ← createRiscvP .srai (mkRISCVImm 63) #[lReg] regType
    let intMax ← createRiscvP .srli (mkRISCVImm 1) #[minusOne] regType
    let overflow ← createRiscvP .xor () #[lReg, unshifted] regType
    let sat ← createRiscvP .xor () #[sign, intMax] regType
    signedSatSelectP regType shifted overflow sat

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence
    (see `sshlSat_pattern`). -/
def sshlSat : Puddle.CompiledPattern OpCode := sshlSat_pattern.compile

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__ushl__sat 2 (isIntTypeOfWidth [64]) fun regType operands => do
    let lReg ← createCastP operands[0]! regType
    let rReg ← createCastP operands[1]! regType
    let shifted ← createRiscvP .sll () #[lReg, rReg] regType
    let unshifted ← createRiscvP .srl () #[shifted, rReg] regType
    let lostBits ← createRiscvP .xor () #[lReg, unshifted] regType
    let noOverflow ← createRiscvP .sltiu (mkRISCVImm 1) #[lostBits] regType
    let overflowMask ← createRiscvP .addi (mkRISCVImm (-1)) #[noOverflow] regType
    createRiscvP .or () #[overflowMask, shifted] regType

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence
    (see `ushlSat_pattern`). -/
def ushlSat : Puddle.CompiledPattern OpCode := ushlSat_pattern.compile

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max`.
    LLVM's RV64+Zbb lowering (`neg a1, a0; max a0, a0, a1`). The `neg` wraps
    `intMin` back to `intMin`, so this is correct for both the
    `is_int_min_poison` and non-poison forms of the intrinsic. -/
def abs_pattern : Puddle.Pattern OpCode :=
  lowerOpP .intr__abs 1 (isIntTypeOfWidth [64]) fun regType operands => do
    let xReg ← createCastP operands[0]! regType
    let neg ← createRiscvP .neg () #[xReg] regType
    createRiscvP .max () #[xReg, neg] regType

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max` (see `abs_pattern`). -/
def abs : Puddle.CompiledPattern OpCode := abs_pattern.compile

/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror (riscv.rorw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr64 : Puddle.CompiledPattern OpCode := fshr64_pattern.compile

def fshr32 : Puddle.CompiledPattern OpCode := fshr32_pattern.compile

/-- The amount of a funnel shift by `amt` on `bw`-bit values: it is taken modulo the bit width. -/
def fshAmount (bw : Nat) (amt : Int) : Int :=
  ((amt % bw) + bw) % bw

/--
  `llvm.intr.fshl`/`llvm.intr.fshr` with identical data operands and a constant shift amount `amt`
  is a constant rotate, lowered to `riscvOp` (`riscv.rori`/`riscv.roriw`) with the immediate
  `imm amt`.
-/
def lowerFshConst (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv) (imm : Int → Int)
    (h : propertiesOf (OpCode.riscv riscvOp) = RISCVImmediateProperties := by rfl) :
    Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let valType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let val ← Puddle.MatchProg.value valType
      let (amt, amtType, amtProps) ← matchConstantIntP
      let resType ← Puddle.MatchProg.type (Attr := IntegerType) (·.bitwidth == bw)
      let _ ← Puddle.MatchProg.root (.llvm llvmOp) #[val, val, amt] #[resType]
      return (resType, val, amtType, amtProps))
    (fun (resType, val, amtType, amtProps) => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let valReg ← createCastP val regType
      let rotProps ← Puddle.CreateProg.applyNative
        (Outputs := Puddle.Handle OpCode (.prop (.riscv riscvOp))) (amtType, amtProps)
        fun (amtType, amtProps) =>
          (constIntValue? amtType amtProps).map fun amt => cast h.symm (mkRISCVImm (imm amt))
      let rot ← createRiscvWithP riscvOp rotProps #[valReg] regType
      createCastP rot resType)
    (fun res => res)

/-- llvm.intr.fshr with identical data operands and a constant shift amount is a
    constant rotate-right: -> riscv.rori (mirrors `PatGprImm<rotr, RORI>`). -/
def fshrConst64 : Puddle.CompiledPattern OpCode :=
  (lowerFshConst .intr__fshr 64 .rori (fshAmount 64)).compile

def fshrConst32 : Puddle.CompiledPattern OpCode :=
  (lowerFshConst .intr__fshr 32 .roriw (fshAmount 32)).compile

/-- llvm.intr.fshl with identical data operands and a constant shift amount is a
    constant rotate-left. There is no `roli`, so (like LLVM) it lowers to
    `riscv.rori` with the negated immediate: rotate-left by `sh` == rotate-right by
    `bw - sh` (mod `bw`). -/
def fshlConst64 : Puddle.CompiledPattern OpCode :=
  (lowerFshConst .intr__fshl 64 .rori (fun amt => (64 - fshAmount 64 amt) % 64)).compile

def fshlConst32 : Puddle.CompiledPattern OpCode :=
  (lowerFshConst .intr__fshl 32 .roriw (fun amt => (32 - fshAmount 32 amt) % 32)).compile

/-! ## General (distinct-operand) funnel shift

  A funnel shift whose two data operands differ is a true funnel shift, not a
  rotate, so there is no single Zbb instruction for it. We mirror LLVM's generic
  `TargetLowering::expandFunnelShift` (`SelectionDAG/TargetLowering.cpp`), which
  is the path RV64 baseline takes since `FSHL`/`FSHR` are marked `Expand`. For a
  power-of-two bit width `w` and a variable shift amount `z` (the case a register
  operand always lands in), the expansion is

    fshl x y z = (x << (z % w)) | ((y >> 1) >> ((w-1) - (z % w)))
    fshr x y z = ((x << 1) << ((w-1) - (z % w))) | (y >> (z % w))

  The RISC-V shifts already reduce their amount modulo the register width, so
  `z % w` is just `z` and `(w-1) - (z % w)` is `~z` (both masked by the hardware).
  The `>> 1` / `<< 1` pre-shifts keep the `z % w = 0` case correct (they push the
  inverse shift to a full-width shift-out of zero). i32 uses the `w`-suffixed
  shifts; only the low `w` bits of the `or` matter, so their sign-extension is
  harmless.

  These run after the rotate/const-rotate matchers, so the identical-operand and
  constant-amount special cases still select the cheaper `rol`/`ror`/`rori`. -/

/-- General `llvm.intr.fshl x y z` -> `(x << z) | ((y >> 1) >> ~z)` (see the
    section comment). Handles i64 and i32; the i32 form uses the `w` shifts. -/
def lowerFshlGeneral (bw : Nat) : Puddle.Pattern OpCode :=
  lowerOpP .intr__fshl 3 (isIntTypeOfWidth [bw]) fun regType operands => do
    let x ← createCastP operands[0]! regType
    let y ← createCastP operands[1]! regType
    let z ← createCastP operands[2]! regType
    /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
    let notz ← createRiscvP .xori (mkRISCVImm (-1)) #[z] regType
    /- shx = x << z ; shy = (y >> 1) >> ~z ; result = shx | shy. The i32 form uses
       the `w` shifts (only the low 32 bits of the `or` are observed). -/
    let (shx, shy) ← if bw = 32 then do
        let shx ← createRiscvP .sllw () #[x, z] regType
        let y1 ← createRiscvP .srliw (mkRISCVImm 1) #[y] regType
        let shy ← createRiscvP .srlw () #[y1, notz] regType
        pure (shx, shy)
      else do
        let shx ← createRiscvP .sll () #[x, z] regType
        let y1 ← createRiscvP .srli (mkRISCVImm 1) #[y] regType
        let shy ← createRiscvP .srl () #[y1, notz] regType
        pure (shx, shy)
    createRiscvP .or () #[shx, shy] regType

/-- General `llvm.intr.fshl` (`i64`) -> shift/or expansion (see `lowerFshlGeneral`). -/
def fshlGeneral64 : Puddle.CompiledPattern OpCode := (lowerFshlGeneral 64).compile

/-- General `llvm.intr.fshl` (`i32`) -> shift/or expansion (see `lowerFshlGeneral`). -/
def fshlGeneral32 : Puddle.CompiledPattern OpCode := (lowerFshlGeneral 32).compile

/-- General `llvm.intr.fshr x y z` -> `((x << 1) << ~z) | (y >> z)` (see the
    section comment). Handles i64 and i32; the i32 form uses the `w` shifts. -/
def lowerFshrGeneral (bw : Nat) : Puddle.Pattern OpCode :=
  lowerOpP .intr__fshr 3 (isIntTypeOfWidth [bw]) fun regType operands => do
    let x ← createCastP operands[0]! regType
    let y ← createCastP operands[1]! regType
    let z ← createCastP operands[2]! regType
    /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
    let notz ← createRiscvP .xori (mkRISCVImm (-1)) #[z] regType
    /- shx = (x << 1) << ~z ; shy = y >> z ; result = shx | shy. The i32 form uses
       the `w` shifts (only the low 32 bits of the `or` are observed). -/
    let (shx, shy) ← if bw = 32 then do
        let x1 ← createRiscvP .slliw (mkRISCVImm 1) #[x] regType
        let shx ← createRiscvP .sllw () #[x1, notz] regType
        let shy ← createRiscvP .srlw () #[y, z] regType
        pure (shx, shy)
      else do
        let x1 ← createRiscvP .slli (mkRISCVImm 1) #[x] regType
        let shx ← createRiscvP .sll () #[x1, notz] regType
        let shy ← createRiscvP .srl () #[y, z] regType
        pure (shx, shy)
    createRiscvP .or () #[shx, shy] regType

/-- General `llvm.intr.fshr` (`i64`) -> shift/or expansion (see `lowerFshrGeneral`). -/
def fshrGeneral64 : Puddle.CompiledPattern OpCode := (lowerFshrGeneral 64).compile

/-- General `llvm.intr.fshr` (`i32`) -> shift/or expansion (see `lowerFshrGeneral`). -/
def fshrGeneral32 : Puddle.CompiledPattern OpCode := (lowerFshrGeneral 32).compile

/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst_pattern : Puddle.Pattern OpCode :=
  Puddle.Pattern.Builder
    (do
      let resType ← Puddle.MatchProg.type (Attr := TypeAttr)
      let _ ← Puddle.MatchProg.root (.llvm .mlir__poison) #[] #[resType]
      return resType)
    (fun resType => do
      let regType ← Puddle.CreateProg.type (RegisterType.mk none)
      let zero ← createRiscvP .li (mkRISCVImm 0) #[] regType
      createCastP zero resType)
    (fun res => res)

/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst : Puddle.CompiledPattern OpCode := poisonConst_pattern.compile

/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze : Puddle.CompiledPattern OpCode :=
  (lowerRegCast .freeze fun opType resType =>
    isIntTypeOfWidth [64, 32] opType && isIntTypeOfWidth [64, 32] resType).compile

/-! # Memory intrinsics -/

/-- A constant-length `memcpy`/`memset` is expanded inline only if it takes at most this
  many stores, as with LLVM's RISC-V `MaxStoresPerMemcpy`/`MaxStoresPerMemset`. -/
def memMaxStores : Nat := 8

/-- The `llvm.align` attribute of argument `i` of a memory intrinsic, or 1 if absent. -/
def memArgAlign (props : LLVMMemIntrinsicProperties) (i : Nat) : Nat := Id.run do
  let some attrs := props.arg_attrs | return 1
  let some (.dictionaryAttr dict) := attrs.value[i]? | return 1
  let some (_, .integerAttr align) := dict.entries.find? (·.1 == "llvm.align".toUTF8) | return 1
  return align.value.toNat

/-- The `(offset, width)` accesses covering `len` bytes, widest first, each at most 8 bytes
  wide and no wider than `align`. Since the widths are decreasing powers of two starting at
  offset 0, every access is naturally aligned. -/
def memAccesses (len align : Nat) : Array (Nat × Nat) := Id.run do
  let mut accesses := #[]
  let mut offset := 0
  for width in [8, 4, 2, 1] do
    if width ≤ align then
      for _ in [0:(len - offset) / width] do
        accesses := accesses.push (offset, width)
        offset := offset + width
  return accesses

/--
  Lower `llvm.intr.memcpy` and `llvm.intr.memset`. A constant length that takes at most
  `memMaxStores` accesses is expanded into loads and stores; anything else becomes a
  `riscv_cf.call` to the C library function. Accesses are never wider than the known
  alignment, so the expansion never introduces a misaligned access.
-/
def memIntrinsic_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let isMemset := op.getOpType! ctx.raw = Llvm.intr__memset
  if !isMemset && op.getOpType! ctx.raw ≠ Llvm.intr__memcpy then return (ctx, none)
  let props : LLVMMemIntrinsicProperties :=
    if isMemset then op.getProperties! ctx.raw Llvm.intr__memset
    else op.getProperties! ctx.raw Llvm.intr__memcpy
  let operands := op.getOperands! ctx.raw
  /- `src` is the source pointer of a `memcpy` and the fill byte of a `memset`. -/
  let (dst, src, len) := (operands[0]!, operands[1]!, operands[2]!)
  let align := if isMemset then memArgAlign props 0
    else min (memArgAlign props 0) (memArgAlign props 1)
  let accesses? : Option (Array (Nat × Nat)) := do
    let len ← matchConstantIntVal len ctx.raw
    guard (0 ≤ len ∧ len ≤ 8 * memMaxStores)
    let accesses := memAccesses len.toNat align
    guard (accesses.size ≤ memMaxStores)
    return accesses
  let (ctx, dstCast) ← castToRegLocal ctx dst
  let dstReg := dstCast.getResult 0
  match accesses? with
  | none =>
    let (ctx, srcCast) ← castToRegLocal ctx src
    let (ctx, lenCast) ← castToRegLocal ctx len
    /- `memset` takes its fill byte as an `int`, so zero-extend the `i8`. -/
    let (ctx, argOps) ← if isMemset then do
        let (ctx, ext) ← createRISCVUnitLocal ctx .zextb rfl #[srcCast.getResult 0]
        pure (ctx, #[srcCast, ext])
      else pure (ctx, #[srcCast])
    let callee : FlatSymbolRefAttr := ⟨if isMemset then "@memset" else "@memcpy"⟩
    let (ctx, callOp) ← WfRewriter.createOp! ctx Riscv_Cf.call #[]
        #[dstReg, argOps.back!.getResult 0, lenCast.getResult 0] #[] #[]
        (RISCVCallProperties.mk (some callee)) none
    return (ctx, some (#[dstCast] ++ argOps ++ #[lenCast, callOp], #[]))
  | some accesses =>
    let mut ctx := ctx
    let mut ops := #[dstCast]
    /- The source register of a `memcpy`; the value to store for a `memset`. Narrower stores
       take the low bits of the 64-bit splat of the fill byte. -/
    let mut srcReg := dstReg
    if isMemset && !accesses.all (·.2 = 1) then
      match matchConstantIntVal src ctx.raw with
      | some c =>
        let (ctx', li) ← createRISCVImmLocal ctx .li rfl #[] ((c % 256) * 0x0101010101010101)
        ctx := ctx'; ops := ops.push li; srcReg := li.getResult 0
      | none =>
        let (ctx', srcCast) ← castToRegLocal ctx src
        let (ctx', ext) ← createRISCVUnitLocal ctx' .zextb rfl #[srcCast.getResult 0]
        let (ctx', ones) ← createRISCVImmLocal ctx' .li rfl #[] 0x0101010101010101
        let (ctx', splat) ← createRISCVUnitLocal ctx' .mul rfl
            #[ext.getResult 0, ones.getResult 0]
        ctx := ctx'; ops := ops ++ #[srcCast, ext, ones, splat]; srcReg := splat.getResult 0
    else
      let (ctx', srcCast) ← castToRegLocal ctx src
      ctx := ctx'; ops := ops.push srcCast; srcReg := srcCast.getResult 0
    for (offset, width) in accesses do
      let memProps := RISCVMemProperties.mk (BitVec.ofNat 64 offset) props.isVolatile
      let mut val := srcReg
      if !isMemset then
        let (ctx', ld) ← createLoadLocal ctx width srcReg memProps
        ctx := ctx'; ops := ops.push ld; val := ld.getResult 0
      let (ctx', st) ← createStoreLocal ctx width val dstReg memProps
      ctx := ctx'; ops := ops.push st
    return (ctx, some (ops, #[]))

/-- `llvm.intr.memcpy` / `llvm.intr.memset` -> loads and stores, or a libcall. -/
def memIntrinsic (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite memIntrinsic_local rewriter op opInBounds

/-! # Pass implementation -/

def ISelPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Early loop: address folding, fixed stack allocations and memory intrinsic
     expansion must inspect LLVM constants before the per-op lowerings consume them. -/
  let early := RewritePattern.GreedyRewritePattern <|
    #[lifetimeStart.run, lifetimeEnd.run, alloca, memIntrinsic] ++
    loadPatterns.map (·.run) ++ storePatterns.map (·.run)
  let ctx ← match RewritePattern.applyInContext early ctx with
  | none => throw "Error while applying early memory-lowering patterns"
  | some ctx => pure ctx
  /- Main loop: the existing per-op lowerings. -/
  let pattern := RewritePattern.GreedyRewritePattern <|
    #[selectCzeroeqz.run, selectCzeronez.run, selectGeneral.run,
      ctlz32.run, ctlz64.run, cttz32.run, cttz64.run, ctpop32.run, ctpop64.run,
      bswap64.run, bswap32.run, bitreverse64.run, bitreverse32.run,
      constant.run, addressof, add32.run, add64.run, and.run, ashr64.run, ashr32.run, ashr8.run] ++
    icmpPatterns.map (·.run) ++
    #[or.run, xor32.run, xor64.run, mul32.run, mul64.run,
      sdiv32.run, sdiv64.run, udiv32.run, udiv64.run, srem32.run, srem64.run, urem32.run, urem64.run,
      sext32.run, sext16.run, sext8.run, zext32.run, zext16.run, zext8.run, trunc.run,
      shl64.run, shl32.run, lshr64.run, lshr32.run, sub64.run, sub32.run, bitcast.run] ++
    loadPatterns.map (·.run) ++ getelementptrPatterns.map (·.run) ++ storePatterns.map (·.run) ++
    #[smax64.run, smax32.run, smin64.run, smin32.run, umax.run, umin.run,
      saddSat.run, ssubSat.run, uaddSat.run, usubSat.run, sshlSat.run, ushlSat.run, abs.run,
      fshlConst64.run, fshlConst32.run, fshrConst64.run, fshrConst32.run,
      fshl64.run, fshl32.run, fshr64.run, fshr32.run,
      fshlGeneral64.run, fshlGeneral32.run, fshrGeneral64.run, fshrGeneral32.run,
      poisonConst.run, freeze.run]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying main instruction-selection patterns"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := fun _ => ISelPass.impl }
