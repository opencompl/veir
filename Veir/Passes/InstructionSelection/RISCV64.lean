module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
import Veir.DataLayout.RISCV64
import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Interfaces.FunctionInterfaces
import Veir.Passes.Matching.LLVM.Basic
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
  `riscv.sextw` for the signed min/max `i32` arms, since `castToReg`'s zero-extension does not
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
    `castToReg` zero-extends) then `riscv.max`. -/
def smax32_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__smax (fun t => t.bitwidth == 32) .max () (extend := some ⟨.sextw, ()⟩)

/-- `llvm.intr.smin` (`i64`) -> `riscv.min`. -/
def smin64_pattern : Veir.Puddle.Pattern OpCode :=
  lowerBinary .intr__smin (fun t => t.bitwidth == 64) .min ()

/-- `llvm.intr.smin` (`i32`) -> sign-extend (so negative values order correctly, since
    `castToReg` zero-extends) then `riscv.min`. -/
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



def add64 : Puddle.CompiledPattern OpCode := add64_pattern.compile

def add32 : Puddle.CompiledPattern OpCode := add32_pattern.compile

def and : Puddle.CompiledPattern OpCode := and_pattern.compile

def or : Puddle.CompiledPattern OpCode := or_pattern.compile

def xor64 : Puddle.CompiledPattern OpCode := xor64_pattern.compile

def xor32 : Puddle.CompiledPattern OpCode := xor32_pattern.compile

def mul64 : Puddle.CompiledPattern OpCode := mul64_pattern.compile

def mul32 : Puddle.CompiledPattern OpCode := mul32_pattern.compile

def sdiv64 : Puddle.CompiledPattern OpCode := sdiv64_pattern.compile

def sdiv32 : Puddle.CompiledPattern OpCode := sdiv32_pattern.compile

def udiv64 : Puddle.CompiledPattern OpCode := udiv64_pattern.compile

def udiv32 : Puddle.CompiledPattern OpCode := udiv32_pattern.compile

def srem64 : Puddle.CompiledPattern OpCode := srem64_pattern.compile

def srem32 : Puddle.CompiledPattern OpCode := srem32_pattern.compile

def urem64 : Puddle.CompiledPattern OpCode := urem64_pattern.compile

def urem32 : Puddle.CompiledPattern OpCode := urem32_pattern.compile

def sub64 : Puddle.CompiledPattern OpCode := sub64_pattern.compile

def sub32 : Puddle.CompiledPattern OpCode := sub32_pattern.compile

def sext8 : Puddle.CompiledPattern OpCode := sext8_pattern.compile

def sext16 : Puddle.CompiledPattern OpCode := sext16_pattern.compile

def sext32 : Puddle.CompiledPattern OpCode := sext32_pattern.compile

def zext8 : Puddle.CompiledPattern OpCode := zext8_pattern.compile

def zext16 : Puddle.CompiledPattern OpCode := zext16_pattern.compile

def zext32 : Puddle.CompiledPattern OpCode := zext32_pattern.compile

def smax64 : Puddle.CompiledPattern OpCode := smax64_pattern.compile

def smax32 : Puddle.CompiledPattern OpCode := smax32_pattern.compile

def smin64 : Puddle.CompiledPattern OpCode := smin64_pattern.compile

def smin32 : Puddle.CompiledPattern OpCode := smin32_pattern.compile

def umax : Puddle.CompiledPattern OpCode := umax_pattern.compile

def umin : Puddle.CompiledPattern OpCode := umin_pattern.compile

def fshl64 : Puddle.CompiledPattern OpCode := fshl64_pattern.compile

def fshl32 : Puddle.CompiledPattern OpCode := fshl32_pattern.compile

def fshr64 : Puddle.CompiledPattern OpCode := fshr64_pattern.compile

def fshr32 : Puddle.CompiledPattern OpCode := fshr32_pattern.compile

/-! ## Puddle creation helpers -/

open Puddle

private abbrev ValueHandle := Handle OpCode .value
private abbrev TypeHandle := Handle OpCode .type

/-- Cast a matched value into an unallocated RISC-V register. -/
def castToReg (value : ValueHandle) : CreateProg.Builder ValueHandle := do
  let regType ← CreateProg.type (RegisterType.mk none)
  let props ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
  let op ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[value] #[regType] props
  return op.res[0]!

/-- Cast the selected register back to the matched LLVM result type. -/
def castFromReg (value : ValueHandle) (type : TypeHandle) : CreateProg.Builder CreatedOpHandle := do
  let props ← CreateProg.property (.builtin .unrealized_conversion_cast) ()
  CreateProg.operation (.builtin .unrealized_conversion_cast) #[value] #[type] props

/-- Emit a register-result instruction with concrete properties. -/
def emitRISCV (op : Riscv) (operands : Array ValueHandle) (props : Riscv.propertiesOf op) :
    CreateProg.Builder ValueHandle := do
  let regType ← CreateProg.type (RegisterType.mk none)
  let props ← CreateProg.property (.riscv op) props
  let result ← CreateProg.operation (.riscv op) operands #[regType] props
  return result.res[0]!

def emitUnit (op : Riscv) (h : Riscv.propertiesOf op = Unit) (operands : Array ValueHandle) :
    CreateProg.Builder ValueHandle := emitRISCV op operands (cast h.symm ())

def emitImm (op : Riscv) (h : Riscv.propertiesOf op = RISCVImmediateProperties)
    (operands : Array ValueHandle) (value : Int) : CreateProg.Builder ValueHandle :=
  emitRISCV op operands (cast h.symm (RISCVImmediateProperties.mk (BitVec.ofInt 64 value)))

/-- Lower an integer operation through a register instruction sequence. -/
def lowerIntSequence (op : Llvm) (bw arity : Nat)
    (emit : Array ValueHandle → CreateProg.Builder ValueHandle) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let args ← (Array.range arity).mapM (fun _ => MatchProg.value type)
      let _ ← MatchProg.root (.llvm op) args #[type]
      return (type, args))
    (fun (type, args) => do
      let regs ← args.mapM castToReg
      let result ← emit regs
      castFromReg result type)
    (fun result => result)

/-- Decode a constant using its SSA result width, including signed attribute encodings. -/
def constantIntValue (type : TypeAttr) (props : LLVMConstantProperties) : Option Int := do
  let .integerType t := type.val | none
  let .integer attr := props.value | none
  return (BitVec.ofInt t.bitwidth (decodeLLVMIntegerConstant attr)).toInt

/-- A structural LLVM integer constant matcher, optionally restricted to zero. -/
def matchIntConstant (type : TypeHandle) (zero : Bool := false) :
    MatchProg.Builder (OpHandle (.llvm .mlir__constant)) := do
  let op ← MatchProg.operation (.llvm .mlir__constant) #[] #[type]
      (fun props => match props.value with | .integer _ => true | _ => false)
  if zero then
    MatchProg.matchNative (type, op.properties)
      (fun (type, props) => constantIntValue type props == some 0)
  return op

/-! ## Bit permutations and constants -/

/-- One SWAR bit-reversal stage: `((x & mask) << shamt) | ((x >> shamt) & mask)`. -/
def bitreverseStage (mask shamt : Int) (input : ValueHandle) : CreateProg.Builder ValueHandle := do
  let maskReg ← emitImm .li rfl #[] mask
  let low ← emitUnit .and rfl #[maskReg, input]
  let lowShift ← emitImm .slli rfl #[low] shamt
  let highShift ← emitImm .srli rfl #[input] shamt
  let high ← emitUnit .and rfl #[maskReg, highShift]
  emitUnit .or rfl #[lowShift, high]

/-- `rev8` reverses eight bytes; shift the i32 result down from the upper half. -/
def bswap_pattern (bw : Nat) : Pattern OpCode :=
  lowerIntSequence .intr__bswap bw 1 fun regs => do
    let result ← emitUnit .rev8 rfl #[regs[0]!]
    if bw == 32 then emitImm .srli rfl #[result] 32 else pure result

def bswap : Array (CompiledPattern OpCode) :=
  #[32, 64].map (fun bw => (bswap_pattern bw).compile)

/-- Reverse bits within bytes with SWAR, then reverse their byte order. -/
def bitreverse_pattern (bw : Nat) : Pattern OpCode :=
  lowerIntSequence .intr__bitreverse bw 1 fun regs => do
    let x1 ← bitreverseStage (if bw == 32 then 0x55555555 else 0x5555555555555555) 1 regs[0]!
    let x2 ← bitreverseStage (if bw == 32 then 0x33333333 else 0x3333333333333333) 2 x1
    let x3 ← bitreverseStage (if bw == 32 then 0x0f0f0f0f else 0x0f0f0f0f0f0f0f0f) 4 x2
    let result ← emitUnit .rev8 rfl #[x3]
    if bw == 32 then emitImm .srli rfl #[result] 32 else pure result

def bitreverse : Array (CompiledPattern OpCode) :=
  #[32, 64].map (fun bw => (bitreverse_pattern bw).compile)

/-- Materialize an LLVM integer constant of at most 64 bits in one register. -/
def constant_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth ≤ 64)
      let root ← MatchProg.root (.llvm .mlir__constant) #[] #[type]
        (fun props => match props.value with | .integer attr => attr.type.bitwidth ≤ 64 | _ => false)
      return (type, root.properties))
    (fun (type, props) => do
      let imm : Handle OpCode (.prop (.riscv .li)) ← CreateProg.applyNative (type, props)
        (fun (type, props) => do
          let value ← constantIntValue type props
          return RISCVImmediateProperties.mk (BitVec.ofInt 64 value))
      let regType ← CreateProg.type (RegisterType.mk none)
      let result ← CreateProg.operation (.riscv .li) #[] #[regType] imm
      castFromReg result.res[0]! type)
    (fun result => result)

def constant : CompiledPattern OpCode := constant_pattern.compile

/-! ## Shifts and comparisons -/

/-- Shifts accept both integer and byte values of width 32 or 64. -/
def lowerByteShift (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (h : Riscv.propertiesOf riscvOp = Unit) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := TypeAttr)
        (fun t => getIntByteTypeBitwidth t == some bw)
      let rhsType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let lhs ← MatchProg.value type
      let rhs ← MatchProg.value rhsType
      let _ ← MatchProg.root (.llvm llvmOp) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (type, lhs, rhs) => do
      let lhs ← castToReg lhs
      let rhs ← castToReg rhs
      let result ← emitUnit riscvOp h #[lhs, rhs]
      castFromReg result type)
    (fun result => result)

def shl : Array (CompiledPattern OpCode) :=
  #[(lowerByteShift .shl 32 .sllw rfl).compile, (lowerByteShift .shl 64 .sll rfl).compile]

def lshr : Array (CompiledPattern OpCode) :=
  #[(lowerByteShift .lshr 32 .srlw rfl).compile, (lowerByteShift .lshr 64 .srl rfl).compile]

/-- Sign-extend i8 before `sra`; i32 uses `sraw`. -/
def ashr_pattern (bw : Nat) : Pattern OpCode :=
  lowerIntSequence .ashr bw 2 fun regs => do
    let lhs ← if bw == 8 then emitUnit .sextb rfl #[regs[0]!] else pure regs[0]!
    if bw == 32 then emitUnit .sraw rfl #[lhs, regs[1]!]
    else emitUnit .sra rfl #[lhs, regs[1]!]

def ashr : Array (CompiledPattern OpCode) :=
  #[8, 32, 64].map (fun bw => (ashr_pattern bw).compile)

/-- Narrow comparisons sign-extend both operands, preserving signed and unsigned order. -/
def icmpExtend (bw : Nat) (value : ValueHandle) : CreateProg.Builder ValueHandle :=
  if bw == 32 then emitUnit .sextw rfl #[value]
  else if bw == 8 then emitUnit .sextb rfl #[value]
  else pure value

/-- The ten LLVM comparison predicates, with zero-RHS eq/ne peepholes tried first. -/
def icmp_pattern (bw : Nat) (pred : Data.LLVM.IntPred) (zero : Bool := false) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let resultType ← MatchProg.type (Attr := IntegerType)
      let lhs ← MatchProg.value type
      let rhs ← if zero then do
          let constant ← matchIntConstant type true
          pure constant.res[0]!
        else MatchProg.value type
      let _ ← MatchProg.root (.llvm .icmp) #[lhs, rhs] #[resultType]
        (fun props => props.predicate == pred)
      return (resultType, lhs, rhs))
    (fun (resultType, lhs, rhs) => do
      let lhs ← castToReg lhs
      let rhs ← castToReg rhs
      let lhs ← icmpExtend bw lhs
      let rhs ← icmpExtend bw rhs
      let result ← match pred with
        | .eq => do
          let diff ← if zero then pure lhs else emitUnit .xor rfl #[rhs, lhs]
          emitImm .sltiu rfl #[diff] 1
        | .ne => do
          let diff ← if zero then pure lhs else emitUnit .xor rfl #[rhs, lhs]
          let zero ← emitImm .li rfl #[] 0
          emitUnit .sltu rfl #[zero, diff]
        | .slt => emitUnit .slt rfl #[lhs, rhs]
        | .sgt => emitUnit .slt rfl #[rhs, lhs]
        | .ult => emitUnit .sltu rfl #[lhs, rhs]
        | .ugt => emitUnit .sltu rfl #[rhs, lhs]
        | .sge => do
          let cmp ← emitUnit .slt rfl #[lhs, rhs]
          emitImm .xori rfl #[cmp] 1
        | .sle => do
          let cmp ← emitUnit .slt rfl #[rhs, lhs]
          emitImm .xori rfl #[cmp] 1
        | .uge => do
          let cmp ← emitUnit .sltu rfl #[lhs, rhs]
          emitImm .xori rfl #[cmp] 1
        | .ule => do
          let cmp ← emitUnit .sltu rfl #[rhs, lhs]
          emitImm .xori rfl #[cmp] 1
      castFromReg result resultType)
    (fun result => result)

def icmp : Array (CompiledPattern OpCode) :=
  #[8, 32, 64].flatMap fun bw =>
    #[(icmp_pattern bw .eq true).compile, (icmp_pattern bw .ne true).compile] ++
    #[Data.LLVM.IntPred.eq, .ne, .slt, .sgt, .ult, .ugt, .sge, .sle, .uge, .ule].map
      (fun pred => (icmp_pattern bw pred).compile)

/-! ## Casts -/

/-- Lower a unary operation by a register round trip, retaining the source/result type guards. -/
def lowerCast (llvmOp : Llvm) (typeMatcher : TypeAttr → Bool)
    (guardTypes : TypeAttr × TypeAttr → Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let opType ← MatchProg.type (Attr := TypeAttr) typeMatcher
      let resType ← MatchProg.type (Attr := TypeAttr) typeMatcher
      let operand ← MatchProg.value opType
      let _ ← MatchProg.root (.llvm llvmOp) #[operand] #[resType]
      MatchProg.matchNative (opType, resType) guardTypes
      return (operand, resType))
    (fun (operand, resType) => do
      let reg ← castToReg operand
      castFromReg reg resType)
    (fun result => result)

/-- Truncate integer-to-integer or byte-to-byte, with source width at most 64. -/
def trunc_pattern : Pattern OpCode :=
  lowerCast .trunc (fun t => (getIntByteTypeBitwidth t).isSome) fun (src, dst) =>
    let sameKind := match src.val, dst.val with
      | .integerType _, .integerType _ | .byteType _, .byteType _ => true
      | _, _ => false
    match getIntByteTypeBitwidth src, getIntByteTypeBitwidth dst with
    | some srcBw, some dstBw => sameKind && decide (dstBw < srcBw ∧ srcBw ≤ 64)
    | _, _ => false

def trunc : CompiledPattern OpCode := trunc_pattern.compile

def checkBitcastType (t : TypeAttr) : Bool :=
  match t.val with
  | .llvmPointerType _ | .integerType _ | .byteType _ => true
  | _ => false

def isBitcastByteToPtr (opType resType : TypeAttr) : Bool :=
  match opType.val, resType.val with
  | .byteType _, .llvmPointerType _ => true
  | _, _ => false

/-- Integer, byte and pointer bitcasts use a register round trip, excluding byte-to-pointer. -/
def bitcast_pattern : Pattern OpCode :=
  lowerCast .bitcast (fun t => checkBitcastType t) fun (src, dst) =>
    !isBitcastByteToPtr src dst &&
    match Attribute.bitwidthOfType src, Attribute.bitwidthOfType dst with
    | some srcBw, some dstBw => decide (srcBw ∈ [8, 16, 32, 64] ∧ dstBw ∈ [8, 16, 32, 64])
    | _, _ => false

def bitcast : CompiledPattern OpCode := bitcast_pattern.compile

def freeze_pattern : Pattern OpCode :=
  lowerCast .freeze (fun t => match t.val with
    | .integerType t => t.bitwidth = 32 ∨ t.bitwidth = 64
    | _ => false) (fun _ => true)

def freeze : CompiledPattern OpCode := freeze_pattern.compile

/-- Poison may be refined to zero; retain its original result type. -/
def poisonConst_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := TypeAttr)
      let _ ← MatchProg.root (.llvm .mlir__poison) #[] #[type]
      return type)
    (fun type => do
      let reg ← emitImm .li rfl #[] 0
      castFromReg reg type)
    (fun result => result)

def poisonConst : CompiledPattern OpCode := poisonConst_pattern.compile

/-! ## Zicond selects -/

/-- Zero-arm forms precede the general branchless select. -/
def select_pattern (zeroTrue zeroFalse : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t =>
        t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ (t.bitwidth = 1 ∧ !zeroTrue ∧ !zeroFalse))
      let condType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond ← MatchProg.value condType
      let tval ← if zeroTrue then do
          let constant ← matchIntConstant type true
          pure constant.res[0]!
        else MatchProg.value type
      let fval ← if zeroFalse then do
          let constant ← matchIntConstant type true
          pure constant.res[0]!
        else MatchProg.value type
      let _ ← MatchProg.root (.llvm .select) #[cond, tval, fval] #[type]
      return (type, cond, tval, fval))
    (fun (type, cond, tval, fval) => do
      let result ← if zeroFalse then do
          let tval ← castToReg tval
          let cond ← castToReg cond
          emitUnit .czeroeqz rfl #[tval, cond]
        else if zeroTrue then do
          let fval ← castToReg fval
          let cond ← castToReg cond
          emitUnit .czeronez rfl #[fval, cond]
        else do
          let tval ← castToReg tval
          let fval ← castToReg fval
          let cond ← castToReg cond
          let eqz ← emitUnit .czeroeqz rfl #[tval, cond]
          let nez ← emitUnit .czeronez rfl #[fval, cond]
          emitUnit .or rfl #[eqz, nez]
      castFromReg result type)
    (fun result => result)

def selectCzeroeqz : CompiledPattern OpCode := (select_pattern false true).compile
def selectCzeronez : CompiledPattern OpCode := (select_pattern true false).compile
def selectGeneral : CompiledPattern OpCode := (select_pattern false false).compile

/-! ## Saturating i64 arithmetic -/

/-- Select the saturation endpoint when overflow is nonzero. -/
def signedSatSelect (wrapped overflow sat : ValueHandle) : CreateProg.Builder ValueHandle := do
  let wrappedOrZero ← emitUnit .czeronez rfl #[wrapped, overflow]
  let satOrZero ← emitUnit .czeroeqz rfl #[sat, overflow]
  emitUnit .or rfl #[satOrZero, wrappedOrZero]

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__sadd__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let minusOne ← emitImm .li rfl #[] (-1)
    let sum ← emitUnit .add rfl #[lReg, rReg]
    let rhsSign ← emitImm .srli rfl #[rReg] 63
    let carryLike ← emitUnit .slt rfl #[sum, lReg]
    let sumSign ← emitImm .srai rfl #[sum] 63
    let intMin ← emitImm .slli rfl #[minusOne] 63
    let overflow ← emitUnit .xor rfl #[rhsSign, carryLike]
    let sat ← emitUnit .xor rfl #[sumSign, intMin]
    signedSatSelect (sum) (overflow) (sat)

def saddSat : CompiledPattern OpCode := saddSat_pattern.compile

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__ssub__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let minusOne ← emitImm .li rfl #[] (-1)
    let diff ← emitUnit .sub rfl #[lReg, rReg]
    let cmp ← emitUnit .slt rfl #[lReg, rReg]
    let diffSignBit ← emitImm .srli rfl #[diff] 63
    let diffSign ← emitImm .srai rfl #[diff] 63
    let intMin ← emitImm .slli rfl #[minusOne] 63
    let overflow ← emitUnit .xor rfl #[cmp, diffSignBit]
    let sat ← emitUnit .xor rfl #[diffSign, intMin]
    signedSatSelect (diff) (overflow) (sat)

def ssubSat : CompiledPattern OpCode := ssubSat_pattern.compile

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__uadd__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let notRhs ← emitImm .xori rfl #[rReg] (-1)
    let minuOp ← emitUnit .minu rfl #[lReg, notRhs]
    let addOp ← emitUnit .add rfl #[minuOp, rReg]
    return (addOp)

def uaddSat : CompiledPattern OpCode := uaddSat_pattern.compile

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__usub__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let maxuOp ← emitUnit .maxu rfl #[lReg, rReg]
    let subOp ← emitUnit .sub rfl #[maxuOp, rReg]
    return (subOp)

def usubSat : CompiledPattern OpCode := usubSat_pattern.compile

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__sshl__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let shifted ← emitUnit .sll rfl #[lReg, rReg]
    let minusOne ← emitImm .li rfl #[] (-1)
    let unshifted ← emitUnit .sra rfl #[shifted, rReg]
    let sign ← emitImm .srai rfl #[lReg] 63
    let intMax ← emitImm .srli rfl #[minusOne] 1
    let overflow ← emitUnit .xor rfl #[lReg, unshifted]
    let sat ← emitUnit .xor rfl #[sign, intMax]
    signedSatSelect (shifted) (overflow) (sat)

def sshlSat : CompiledPattern OpCode := sshlSat_pattern.compile

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat_pattern : Pattern OpCode :=
  lowerIntSequence .intr__ushl__sat 64 2 fun regs => do
    let lReg := regs[0]!
    let rReg := regs[1]!
    let shifted ← emitUnit .sll rfl #[lReg, rReg]
    let unshifted ← emitUnit .srl rfl #[shifted, rReg]
    let lostBits ← emitUnit .xor rfl #[lReg, unshifted]
    let noOverflow ← emitImm .sltiu rfl #[lostBits] 1
    let overflowMask ← emitImm .addi rfl #[noOverflow] (-1)
    let orOp ← emitUnit .or rfl #[overflowMask, shifted]
    return (orOp)

def ushlSat : CompiledPattern OpCode := ushlSat_pattern.compile

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max`.
    LLVM's RV64+Zbb lowering (`neg a1, a0; max a0, a0, a1`). The `neg` wraps
    `intMin` back to `intMin`, so this is correct for both the
    `is_int_min_poison` and non-poison forms of the intrinsic. -/
def abs_pattern : Pattern OpCode :=
  lowerIntSequence .intr__abs 64 1 fun regs => do
    let xReg := regs[0]!
    let negOp ← emitUnit .neg rfl #[xReg]
    let maxOp ← emitUnit .max rfl #[xReg, negOp]
    return (maxOp)

def abs : CompiledPattern OpCode := abs_pattern.compile

/-! ## Constant rotates and general funnel shifts -/

/-- Constant rotate-left uses rotate-right with the negated amount modulo the width. -/
def lowerConstRotate (left : Bool) (bw : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let val ← MatchProg.value type
      let amt ← matchIntConstant type
      let _ ← MatchProg.root (.llvm (if left then .intr__fshl else .intr__fshr))
        #[val, val, amt.res[0]!] #[type]
      return (type, val, amt.properties))
    (fun (type, val, amtProps) => do
      let val ← castToReg val
      let imm : Handle OpCode (.prop (.riscv .rori)) ← CreateProg.applyNative (type, amtProps)
        (fun (type, props) => do
          let amt ← constantIntValue type props
          let sh := ((amt % (bw : Int)) + bw) % bw
          let imm := if left then ((bw : Int) - sh) % bw else sh
          return RISCVImmediateProperties.mk (BitVec.ofInt 64 imm))
      let regType ← CreateProg.type (RegisterType.mk none)
      let result ← if bw == 32 then do
          let imm32 : Handle OpCode (.prop (.riscv .roriw)) ←
            CreateProg.applyNative imm (fun props => some props)
          CreateProg.operation (.riscv .roriw) #[val] #[regType] imm32
        else CreateProg.operation (.riscv .rori) #[val] #[regType] imm
      castFromReg result.res[0]! type)
    (fun result => result)

def fshlConst : Array (CompiledPattern OpCode) :=
  #[32, 64].map (fun bw => (lowerConstRotate true bw).compile)

def fshrConst : Array (CompiledPattern OpCode) :=
  #[32, 64].map (fun bw => (lowerConstRotate false bw).compile)

/-- General fshl: `(x << z) | ((y >> 1) >> ~z)`; general fshr:
  `((x << 1) << ~z) | (y >> z)`. The pre-shift handles a zero shift amount.
  i32 uses word shifts; hardware masks each variable shift amount modulo the width. -/
def lowerFunnelShift (left : Bool) (bw : Nat) : Pattern OpCode :=
  lowerIntSequence (if left then .intr__fshl else .intr__fshr) bw 3 fun regs => do
    let x := regs[0]!
    let y := regs[1]!
    let z := regs[2]!
    let notz ← emitImm .xori rfl #[z] (-1)
    let (shx, shy) ← if left then do
        let shx ← if bw == 32 then emitUnit .sllw rfl #[x, z] else emitUnit .sll rfl #[x, z]
        let y1 ← if bw == 32 then emitImm .srliw rfl #[y] 1 else emitImm .srli rfl #[y] 1
        let shy ← if bw == 32 then emitUnit .srlw rfl #[y1, notz] else emitUnit .srl rfl #[y1, notz]
        pure (shx, shy)
      else do
        let x1 ← if bw == 32 then emitImm .slliw rfl #[x] 1 else emitImm .slli rfl #[x] 1
        let shx ← if bw == 32 then emitUnit .sllw rfl #[x1, notz] else emitUnit .sll rfl #[x1, notz]
        let shy ← if bw == 32 then emitUnit .srlw rfl #[y, z] else emitUnit .srl rfl #[y, z]
        pure (shx, shy)
    emitUnit .or rfl #[shx, shy]

def fshlGeneral : Array (CompiledPattern OpCode) :=
  #[32, 64].map (fun bw => (lowerFunnelShift true bw).compile)

def fshrGeneral : Array (CompiledPattern OpCode) :=
  #[32, 64].map (fun bw => (lowerFunnelShift false bw).compile)

/-! ## Memory operations -/

/-- Allocation size for the single dynamic index form accepted by instruction selection. -/
def gepScale (props : GetelementptrProperties) : Option Nat := do
  guard (props.rawConstantIndices.values = #[(-2147483648 : Int)])
  DataLayout.riscv64.getTypeAllocSize props.elem_type.val

/-- Derive a signed 12-bit address offset from constant-index GEP metadata. -/
def gepOffset (props : GetelementptrProperties) (idxType : TypeAttr)
    (idxProps : LLVMConstantProperties) : Option Int := do
  let scale ← gepScale props
  let idx ← constantIntValue idxType idxProps
  let offset := idx * (scale : Int)
  guard (-2048 ≤ offset ∧ offset ≤ 2047)
  return offset

/-- Match a constant-index address graph for early load/store folding. -/
def matchFoldedAddr : MatchProg.Builder
    (ValueHandle × Handle OpCode (.prop (.llvm .getelementptr)) × TypeHandle ×
      Handle OpCode (.prop (.llvm .mlir__constant)) × ValueHandle) := do
  let ptrType ← MatchProg.type (Attr := TypeAttr)
  let baseType ← MatchProg.type (Attr := TypeAttr)
  let base ← MatchProg.value baseType
  let idxType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
  let idx ← matchIntConstant idxType
  let gep ← MatchProg.operation (.llvm .getelementptr) #[base, idx.res[0]!] #[ptrType]
  MatchProg.matchNative (gep.properties, idxType, idx.properties)
    (fun (props, idxType, idxProps) => (gepOffset props idxType idxProps).isSome)
  return (base, gep.properties, idxType, idx.properties, gep.res[0]!)

/-- Load widths select ld/lw/lh/lb, preserving volatility and any folded offset. -/
def load_pattern (bw : Nat) (rop : Riscv) (h : Riscv.propertiesOf rop = RISCVMemProperties)
    (foldAddr : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let (base, addr, offsetInputs) ← if foldAddr then do
          let (base, gep, idxType, idxProps, addr) ← matchFoldedAddr
          pure (base, addr, some (gep, idxType, idxProps))
        else do
          let ptrType ← MatchProg.type (Attr := TypeAttr)
          let addr ← MatchProg.value ptrType
          pure (addr, addr, none)
      let root ← MatchProg.root (.llvm .load) #[addr] #[type]
      return (type, base, root.properties, offsetInputs))
    (fun (type, base, props, offsetInputs) => do
      let base ← castToReg base
      let memProps : Handle OpCode (.prop (.riscv rop)) ← (match offsetInputs with
        | some (gep, idxType, idxProps) => CreateProg.applyNative (props, gep, idxType, idxProps)
            (fun (props, gep, idxType, idxProps) =>
              (gepOffset gep idxType idxProps).map fun offset =>
                cast h.symm (RISCVMemProperties.mk (BitVec.ofInt 64 offset) props.volatile_))
        | none => CreateProg.applyNative props
            (fun props => some (cast h.symm (RISCVMemProperties.mk 0#64 props.volatile_))))
      let regType ← CreateProg.type (RegisterType.mk none)
      let result ← CreateProg.operation (.riscv rop) #[base] #[regType] memProps
      castFromReg result.res[0]! type)
    (fun result => result)

def load : Array (CompiledPattern OpCode) :=
  #[true, false].flatMap fun foldAddr =>
    #[(load_pattern 8 .lb rfl foldAddr).compile, (load_pattern 16 .lh rfl foldAddr).compile,
      (load_pattern 32 .lw rfl foldAddr).compile, (load_pattern 64 .ld rfl foldAddr).compile]

/-- Store widths select sd/sw/sh/sb; stores have no replacement results. -/
def store_pattern (bw : Nat) (rop : Riscv) (h : Riscv.propertiesOf rop = RISCVMemProperties)
    (foldAddr : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let arg ← MatchProg.value type
      let (base, addr, offsetInputs) ← if foldAddr then do
          let (base, gep, idxType, idxProps, addr) ← matchFoldedAddr
          pure (base, addr, some (gep, idxType, idxProps))
        else do
          let ptrType ← MatchProg.type (Attr := TypeAttr)
          let addr ← MatchProg.value ptrType
          pure (addr, addr, none)
      let root ← MatchProg.root (.llvm .store) #[arg, addr] #[]
      return (arg, base, root.properties, offsetInputs))
    (fun (arg, base, props, offsetInputs) => do
      let base ← castToReg base
      let arg ← castToReg arg
      let memProps : Handle OpCode (.prop (.riscv rop)) ← (match offsetInputs with
        | some (gep, idxType, idxProps) => CreateProg.applyNative (props, gep, idxType, idxProps)
            (fun (props, gep, idxType, idxProps) =>
              (gepOffset gep idxType idxProps).map fun offset =>
                cast h.symm (RISCVMemProperties.mk (BitVec.ofInt 64 offset) props.volatile_))
        | none => CreateProg.applyNative props
            (fun props => some (cast h.symm (RISCVMemProperties.mk 0#64 props.volatile_))))
      CreateProg.operation (.riscv rop) #[arg, base] #[] memProps)
    (fun result => result)

def store : Array (CompiledPattern OpCode) :=
  #[true, false].flatMap fun foldAddr =>
    #[(store_pattern 8 .sb rfl foldAddr).compile, (store_pattern 16 .sh rfl foldAddr).compile,
      (store_pattern 32 .sw rfl foldAddr).compile, (store_pattern 64 .sd rfl foldAddr).compile]

/-- Partition GEP scales into the four Zba forms, a power-of-two shift, and general multiplication. -/
def gepScaleKind (scale : Nat) : Nat :=
  if scale = 1 then 0 else if scale = 2 then 1 else if scale = 4 then 2 else if scale = 8 then 3
  else if 0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64 then 4 else 5

/-- A single dynamic i64 GEP index is scaled by the element's ABI allocation size. -/
def getelementptr_pattern (kind : Nat) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ptrType ← MatchProg.type (Attr := TypeAttr)
      let resType ← MatchProg.type (Attr := TypeAttr)
      let idxType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 64)
      let ptr ← MatchProg.value ptrType
      let idx ← MatchProg.value idxType
      let root ← MatchProg.root (.llvm .getelementptr) #[ptr, idx] #[resType]
        (fun props => ((gepScale props).map gepScaleKind) == some kind)
      return (resType, ptr, idx, root.properties))
    (fun (type, ptr, idx, props) => do
      let ptr ← castToReg ptr
      let idx ← castToReg idx
      let result ← match kind with
        | 0 => emitUnit .add rfl #[ptr, idx]
        | 1 => emitUnit .sh1add rfl #[idx, ptr]
        | 2 => emitUnit .sh2add rfl #[idx, ptr]
        | 3 => emitUnit .sh3add rfl #[idx, ptr]
        | _ => do
          let imm : Handle OpCode (.prop (.riscv .li)) ← CreateProg.applyNative props
            (fun props => do
              let scale ← gepScale props
              let value := if kind == 4 then Nat.log2 scale else scale
              return RISCVImmediateProperties.mk (BitVec.ofNat 64 value))
          let regType ← CreateProg.type (RegisterType.mk none)
          let scaled ← if kind == 4 then do
              let shiftImm : Handle OpCode (.prop (.riscv .slli)) ←
                CreateProg.applyNative imm (fun props => some props)
              let shifted ← CreateProg.operation (.riscv .slli) #[idx] #[regType] shiftImm
              pure shifted.res[0]!
            else do
              let scale ← CreateProg.operation (.riscv .li) #[] #[regType] imm
              emitUnit .mul rfl #[idx, scale.res[0]!]
          emitUnit .add rfl #[ptr, scaled]
      castFromReg result type)
    (fun result => result)

def getelementptr : Array (CompiledPattern OpCode) :=
  (Array.range 6).map (fun kind => (getelementptr_pattern kind).compile)

/-- Inspect the constant-like count, data layout, alignment, and function-entry placement.
  Reject unsupported allocations during matching, before Puddle creates any operations. -/
def allocaStackProperties (ctx : IRContext OpCode) (op : OperationPtr) :
    Option RISCVStackAllocaProperties := do
  let (operands, properties) ← matchOp op ctx Llvm.alloca 1
  guard (!properties.inalloca)
  let func ← op.getParentOp! ctx
  guard (func.isFunctionLike ctx)
  let entry ← FunctionOpInterface.getEntryBlock? func ctx
  guard ((op.get! ctx).parent == some entry)
  let .int _ (.val count) ← operands[0]!.constantValue ctx | none
  let layout ← DataLayout.riscv64.query properties.elem_type.val
  let size := count.toNat * layout.allocSize
  guard (size < 2 ^ 63)
  let alignment : Int := if properties.alignment.value = 0 then layout.abiAlignment
    else properties.alignment.value
  guard (isValidLLVMAlignment alignment && decide (alignment < 2 ^ 63))
  return { size := BitVec.ofNat 64 size, alignment := BitVec.ofInt 64 alignment }

/-- Construct a fixed stack object and cast it back to the matched pointer type. -/
def alloca_pattern : Pattern OpCode :=
  Pattern.Builder
    (do
      let type ← MatchProg.type (Attr := LLVM.PointerType)
      let countType ← MatchProg.type (Attr := TypeAttr)
      let count ← MatchProg.value countType
      let root ← MatchProg.root (.llvm .alloca) #[count] #[type] (fun props => !props.inalloca)
      let stackProps : Handle OpCode (.prop (.riscv_stack .alloca)) ←
        MatchProg.inspectOperation root.op allocaStackProperties
      return (type, stackProps))
    (fun (type, props) => do
      let regType ← CreateProg.type (RegisterType.mk none)
      let stack ← CreateProg.operation (.riscv_stack .alloca) #[] #[regType] props
      castFromReg stack.res[0]! type)
    (fun result => result)

def alloca : CompiledPattern OpCode := alloca_pattern.compile

/-! # Pass implementation -/

def ISelPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Address folding and stack allocations inspect constants before constant selection. -/
  let early := RewritePattern.GreedyRewritePattern
    ((#[alloca] ++ load ++ store).map (·.run))
  let ctx ← match RewritePattern.applyInContext early ctx with
    | none => throw "Error while applying early memory-lowering patterns"
    | some ctx => pure ctx
  /- Keep specialized cases before the general patterns that also match them. -/
  let patterns := #[selectCzeroeqz, selectCzeronez, selectGeneral,
      ctlz32, ctlz64, cttz32, cttz64, ctpop32, ctpop64] ++ bswap ++ bitreverse ++
    #[constant, add32, add64, and] ++ ashr ++ icmp ++
    #[or, xor32, xor64, mul32, mul64, sdiv32, sdiv64, udiv32, udiv64,
      srem32, srem64, urem32, urem64, sext32, sext16, sext8, zext32, zext16, zext8, trunc] ++
    shl ++ lshr ++ #[sub64, sub32, bitcast] ++ load ++ getelementptr ++ store ++
    #[smax64, smax32, smin64, smin32, umax, umin, saddSat, ssubSat, uaddSat, usubSat,
      sshlSat, ushlSat, abs] ++ fshlConst ++ fshrConst ++
    #[fshl64, fshl32, fshr64, fshr32] ++ fshlGeneral ++ fshrGeneral ++ #[poisonConst, freeze]
  let pattern := RewritePattern.GreedyRewritePattern (patterns.map (·.run))
  match RewritePattern.applyInContext pattern ctx with
    | none => throw "Error while applying main instruction-selection patterns"
    | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description := "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := fun _ => ISelPass.impl }
