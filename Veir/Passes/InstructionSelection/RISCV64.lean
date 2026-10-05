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

/--
  Shared shape of the binary RISC-V lowerings that accept both integer and byte values (`shl`/`lshr`):
  match an lhs of width `bw` (an integer or byte type), cast both operands to registers, apply
  `riscvOp`, and cast the result back to the result type.
-/
def lowerByteBinaryW (llvmOp : Llvm) (bw : Nat) (riscvOp : Riscv)
    (riscvProps : propertiesOf (OpCode.riscv riscvOp)) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let lhsType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
          (fun t => getIntByteTypeBitwidth t == some bw)
      let rhsType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
      let resType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
      let lhs ← Veir.Puddle.MatchProg.value lhsType
      let rhs ← Veir.Puddle.MatchProg.value rhsType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let lcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let lcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType] lcastProps
      let rcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let rcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType] rcastProps
      let riscvOpProps ← Veir.Puddle.CreateProg.property (.riscv riscvOp) riscvProps
      let riscvResOp ← Veir.Puddle.CreateProg.operation (.riscv riscvOp)
          #[lcastOp.res[0]!, rcastOp.res[0]!] #[regType] riscvOpProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[riscvResOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.shl` (`i64`) -> `riscv.sll`. -/
def shl64_pattern : Veir.Puddle.Pattern OpCode := lowerByteBinaryW .shl 64 .sll ()

/-- `llvm.shl` (`i32`) -> `riscv.sllw`. -/
def shl32_pattern : Veir.Puddle.Pattern OpCode := lowerByteBinaryW .shl 32 .sllw ()

/-- `llvm.lshr` (`i64`) -> `riscv.srl`. -/
def lshr64_pattern : Veir.Puddle.Pattern OpCode := lowerByteBinaryW .lshr 64 .srl ()

/-- `llvm.lshr` (`i32`) -> `riscv.srlw`. -/
def lshr32_pattern : Veir.Puddle.Pattern OpCode := lowerByteBinaryW .lshr 32 .srlw ()

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
def lowerBswap (bw : Nat) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let resType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
      let x ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm .intr__bswap) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let rev8Props ← Veir.Puddle.CreateProg.property (.riscv .rev8) ()
      let rev8Op ← Veir.Puddle.CreateProg.operation (.riscv .rev8)
          #[castOp.res[0]!] #[regType] rev8Props
      let resOp ← if bw = 32 then do
          let srliProps ← Veir.Puddle.CreateProg.property (.riscv .srli)
              (RISCVImmediateProperties.mk 32#64)
          Veir.Puddle.CreateProg.operation (.riscv .srli) #[rev8Op.res[0]!] #[regType] srliProps
        else
          pure rev8Op
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[resOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.bswap` (`i64`) -> `riscv.rev8`. -/
def bswap64 : Puddle.CompiledPattern OpCode := (lowerBswap 64).compile

/-- `llvm.intr.bswap` (`i32`) -> `riscv.rev8` + `riscv.srli 32`. -/
def bswap32 : Puddle.CompiledPattern OpCode := (lowerBswap 32).compile

/--
  One SWAR bit-reversal stage:
  `((x & mask) << shamt) | ((x >> shamt) & mask)`.
-/
def bitreverseStage (regType : Veir.Puddle.Handle OpCode .type) (mask shamt : Int)
    (input : Veir.Puddle.Handle OpCode .value) :
    Veir.Puddle.CreateProg.Builder (Veir.Puddle.Handle OpCode .value) := do
  let maskProps ← Veir.Puddle.CreateProg.property (.riscv .li)
      (RISCVImmediateProperties.mk (BitVec.ofInt 64 mask))
  let maskOp ← Veir.Puddle.CreateProg.operation (.riscv .li) #[] #[regType] maskProps
  let lowProps ← Veir.Puddle.CreateProg.property (.riscv .and) ()
  let lowOp ← Veir.Puddle.CreateProg.operation (.riscv .and)
      #[maskOp.res[0]!, input] #[regType] lowProps
  let lowShiftProps ← Veir.Puddle.CreateProg.property (.riscv .slli)
      (RISCVImmediateProperties.mk (BitVec.ofInt 64 shamt))
  let lowShiftOp ← Veir.Puddle.CreateProg.operation (.riscv .slli)
      #[lowOp.res[0]!] #[regType] lowShiftProps
  let highShiftProps ← Veir.Puddle.CreateProg.property (.riscv .srli)
      (RISCVImmediateProperties.mk (BitVec.ofInt 64 shamt))
  let highShiftOp ← Veir.Puddle.CreateProg.operation (.riscv .srli)
      #[input] #[regType] highShiftProps
  let highProps ← Veir.Puddle.CreateProg.property (.riscv .and) ()
  let highOp ← Veir.Puddle.CreateProg.operation (.riscv .and)
      #[maskOp.res[0]!, highShiftOp.res[0]!] #[regType] highProps
  let orProps ← Veir.Puddle.CreateProg.property (.riscv .or) ()
  let orOp ← Veir.Puddle.CreateProg.operation (.riscv .or)
      #[lowShiftOp.res[0]!, highOp.res[0]!] #[regType] orProps
  return orOp.res[0]!

/--
  `llvm.intr.bitreverse` -> mask/shift/or stages followed by `riscv.rev8`.
-/
def lowerBitreverse (bw : Nat) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let resType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
      let x ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm .intr__bitreverse) #[x] #[resType]
      return (resType, x))
    (fun (resType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      let resOp ← if bw = 32 then do
          /- Use 32-bit masks so SWAR stages stay within the low 32 bits.
             rev8 brings bits to high 32; srli 32 moves them back down. -/
          let x1 ← bitreverseStage regType 0x55555555 1 castOp.res[0]!
          let x2 ← bitreverseStage regType 0x33333333 2 x1
          let x3 ← bitreverseStage regType 0x0f0f0f0f 4 x2
          let rev8Props ← Veir.Puddle.CreateProg.property (.riscv .rev8) ()
          let rev8Op ← Veir.Puddle.CreateProg.operation (.riscv .rev8) #[x3] #[regType] rev8Props
          let srliProps ← Veir.Puddle.CreateProg.property (.riscv .srli)
              (RISCVImmediateProperties.mk 32#64)
          Veir.Puddle.CreateProg.operation (.riscv .srli) #[rev8Op.res[0]!] #[regType] srliProps
        else do
          let x1 ← bitreverseStage regType 0x5555555555555555 1 castOp.res[0]!
          let x2 ← bitreverseStage regType 0x3333333333333333 2 x1
          let x3 ← bitreverseStage regType 0x0f0f0f0f0f0f0f0f 4 x2
          let rev8Props ← Veir.Puddle.CreateProg.property (.riscv .rev8) ()
          Veir.Puddle.CreateProg.operation (.riscv .rev8) #[x3] #[regType] rev8Props
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[resOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- `llvm.intr.bitreverse` (`i64`) -> mask/shift/or stages followed by `riscv.rev8`. -/
def bitreverse64 : Puddle.CompiledPattern OpCode := (lowerBitreverse 64).compile

/-- `llvm.intr.bitreverse` (`i32`) -> mask/shift/or stages, `riscv.rev8` and `riscv.srli 32`. -/
def bitreverse32 : Puddle.CompiledPattern OpCode := (lowerBitreverse 32).compile

/-- llvm.constant -> riscv.li. Any width up to 64 fits in one register: the constant is
  sign-extended to the 64-bit immediate (see `constant_refinement_le64`). -/
def constant_pattern : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let type ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth ≤ 64)
      let root ← Veir.Puddle.MatchProg.root (.llvm .mlir__constant) #[] #[type]
          (fun props => props.value matches .integer _)
      return (type, root.properties))
    (fun (type, constProps) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let liProps ← Veir.Puddle.CreateProg.applyNative
          (Outputs := Veir.Puddle.Handle OpCode (.prop (.riscv .li))) (type, constProps)
          fun (type, constProps) => do
            let .integerType type' := type.val | none
            let .integer const := constProps.value | none
            return RISCVImmediateProperties.mk
                ((BitVec.ofInt type'.bitwidth const.value).signExtend 64)
      let liOp ← Veir.Puddle.CreateProg.operation (.riscv .li) #[] #[regType] liProps
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[liOp.res[0]!] #[type] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.constant -> riscv.li -/
def constant : Puddle.CompiledPattern OpCode := constant_pattern.compile

/-- llvm.add -> riscv.add -/
def add64 : Puddle.CompiledPattern OpCode := add64_pattern.compile

/-- llvm.add -> riscv.addw (riscv.addw for i32, keeps the result sign-extended) -/
def add32 : Puddle.CompiledPattern OpCode := add32_pattern.compile

/-- llvm.and -> riscv.and (bitwise, so one instruction for every legal width) -/
def and : Puddle.CompiledPattern OpCode := and_pattern.compile

/--
  `llvm.ashr` with an `i64`, `i32`, or `i8` result of width `bw` -> `riscv.sra` (`riscv.sraw` for
  `i32`, which sign-extends the result). An `i8` lhs is sign-extended with `riscv.sextb` first, so
  the arithmetic shift sees its sign bit.
-/
def lowerAshr (bw : Nat) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      /- support `i64`, `i32`, and `i8` -/
      let lhsType ← Veir.Puddle.MatchProg.type (Attr := IntegerType)
          (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 8)
      let rhsType ← Veir.Puddle.MatchProg.type (Attr := IntegerType)
          (fun t => t.bitwidth = 64 ∨ t.bitwidth = 32 ∨ t.bitwidth = 8)
      let resType ← Veir.Puddle.MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == bw)
      let lhs ← Veir.Puddle.MatchProg.value lhsType
      let rhs ← Veir.Puddle.MatchProg.value rhsType
      let _ ← Veir.Puddle.MatchProg.root (.llvm .ashr) #[lhs, rhs] #[resType]
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      /- First, cast the operands to registers -/
      let lcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let lcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[lhs] #[regType] lcastProps
      let rcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let rcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[rhs] #[regType] rcastProps
      let sraOp ← if bw = 8 then do
          let sextbProps ← Veir.Puddle.CreateProg.property (.riscv .sextb) ()
          let sextbOp ← Veir.Puddle.CreateProg.operation (.riscv .sextb)
              #[lcastOp.res[0]!] #[regType] sextbProps
          let sraProps ← Veir.Puddle.CreateProg.property (.riscv .sra) ()
          Veir.Puddle.CreateProg.operation (.riscv .sra)
              #[sextbOp.res[0]!, rcastOp.res[0]!] #[regType] sraProps
        else if bw = 32 then do
          /- sraw for i32 (sign-extends result) -/
          let srawProps ← Veir.Puddle.CreateProg.property (.riscv .sraw) ()
          Veir.Puddle.CreateProg.operation (.riscv .sraw)
              #[lcastOp.res[0]!, rcastOp.res[0]!] #[regType] srawProps
        else do
          let sraProps ← Veir.Puddle.CreateProg.property (.riscv .sra) ()
          Veir.Puddle.CreateProg.operation (.riscv .sra)
              #[lcastOp.res[0]!, rcastOp.res[0]!] #[regType] sraProps
      /- Cast back result for type consistency -/
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[sraOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/-- llvm.ashr -> riscv.sra -/
def ashr64 : Puddle.CompiledPattern OpCode := (lowerAshr 64).compile

/-- llvm.ashr -> riscv.sraw (sign-extends the result) -/
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

  Every arm shares the same prologue (`icmpCastExt`: cast both operands into registers, and
  sign-extend them when they are narrower than a register) and the same epilogue (cast the `i1`
  result back). Only the comparison sequence in between differs (`icmpEmit`). Since the prologue
  depends on the lhs width, there is one Puddle pattern per predicate and lhs width. -/

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

/-- Whether an `llvm.mlir.constant` with result type `type` and properties `props` is the integer
    `0` (as `matchConstantZero`). -/
def isConstantZero (type : TypeAttr) (props : LLVMConstantProperties) : Bool :=
  match type.val, props.value with
  | .integerType t, .integer attr => (BitVec.ofInt t.bitwidth attr.value).toInt == 0
  | _, _ => false

/--
  Shared prologue of every `llvm.icmp` arm: cast both operands into registers and, when `ext` is
  `some e`, sign-extend each register with `e` (`riscv.sextw` for `i32`, `riscv.sextb` for `i8`).
  The cast zero-extends into the register, so without the fixup a negative narrow operand
  would look positive to the 64-bit signed comparison; sign-extension also preserves the unsigned
  order, so the unsigned comparisons stay correct too.

  Returns the two registers to compare.
-/
def icmpCastExt (regType : Veir.Puddle.Handle OpCode .type)
    (lhs rhs : Veir.Puddle.Handle OpCode .value)
    (ext : Option (Σ extOp : Riscv, propertiesOf (OpCode.riscv extOp))) :
    Veir.Puddle.CreateProg.Builder
      (Veir.Puddle.Handle OpCode .value × Veir.Puddle.Handle OpCode .value) := do
  let lcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
  let lcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
      #[lhs] #[regType] lcastProps
  let rcastProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
  let rcastOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
      #[rhs] #[regType] rcastProps
  match ext with
  | none => pure (lcastOp.res[0]!, rcastOp.res[0]!)
  | some ⟨extOp, extProps'⟩ => do
    let extProps ← Veir.Puddle.CreateProg.property (.riscv extOp) extProps'
    let lextOp ← Veir.Puddle.CreateProg.operation (.riscv extOp)
        #[lcastOp.res[0]!] #[regType] extProps
    let rextOp ← Veir.Puddle.CreateProg.operation (.riscv extOp)
        #[rcastOp.res[0]!] #[regType] extProps
    pure (lextOp.res[0]!, rextOp.res[0]!)

/--
  `icmp` arm emitting a register-register comparison `rop` (`slt`/`sltu`/`xor`), whose operands
  are the two comparison registers, swapped when `swap` is set, optionally followed by the
  immediate op `ropImm` applied to its result with the immediate `1`.
  - `slt`/`sgt`/`ult`/`ugt`: just the comparison.
  - `sle`/`sge`/`ule`/`uge`: `slt`/`sltu` then `xori _ 1`.
  - the generic `eq`: `xor` then `sltiu _ 1`.
-/
def icmpEmitCmp (regType : Veir.Puddle.Handle OpCode .type) (a b : Veir.Puddle.Handle OpCode .value)
    (rop : Riscv) (ropProps : propertiesOf (OpCode.riscv rop)) (swap : Bool)
    (ropImm : Option (Σ immOp : Riscv, propertiesOf (OpCode.riscv immOp)) := none) :
    Veir.Puddle.CreateProg.Builder Veir.Puddle.CreatedOpHandle := do
  let (u, v) := if swap then (b, a) else (a, b)
  let cmpProps ← Veir.Puddle.CreateProg.property (.riscv rop) ropProps
  let cmpOp ← Veir.Puddle.CreateProg.operation (.riscv rop) #[u, v] #[regType] cmpProps
  match ropImm with
  | none => pure cmpOp
  | some ⟨immOp, immProps'⟩ => do
    let immProps ← Veir.Puddle.CreateProg.property (.riscv immOp) immProps'
    Veir.Puddle.CreateProg.operation (.riscv immOp) #[cmpOp.res[0]!] #[regType] immProps

/-- The comparison sequence of the `icmp` arm for `pred` on the comparison registers `a` and `b`.
    `zeroRhs` selects the `eq`/`ne`-against-zero peepholes, which only use `a`. -/
def icmpEmit (regType : Veir.Puddle.Handle OpCode .type) (pred : Data.LLVM.IntPred)
    (zeroRhs : Bool) (a b : Veir.Puddle.Handle OpCode .value) :
    Veir.Puddle.CreateProg.Builder Veir.Puddle.CreatedOpHandle :=
  match pred, zeroRhs with
  /- `seqz`: `sltiu a 1`, the `eq`-against-zero peephole. -/
  | .eq, true => do
    let sltiuProps ← Veir.Puddle.CreateProg.property (.riscv .sltiu) icmpOneImm
    Veir.Puddle.CreateProg.operation (.riscv .sltiu) #[a] #[regType] sltiuProps
  | .eq, false => icmpEmitCmp regType a b .xor () true (some ⟨.sltiu, icmpOneImm⟩)
  /- `snez`: `sltu 0 a`, the `ne`-against-zero peephole. The `riscv.li 0` becomes `x0` under
     `riscv-combine` (see `li_zero_to_x0`). -/
  | .ne, true => do
    let liProps ← Veir.Puddle.CreateProg.property (.riscv .li) icmpZeroImm
    let liOp ← Veir.Puddle.CreateProg.operation (.riscv .li) #[] #[regType] liProps
    let sltuProps ← Veir.Puddle.CreateProg.property (.riscv .sltu) ()
    Veir.Puddle.CreateProg.operation (.riscv .sltu) #[liOp.res[0]!, a] #[regType] sltuProps
  /- `sltu 0 (xor b a)` (`snez` of the difference): the generic `ne`. -/
  | .ne, false => do
    let xorProps ← Veir.Puddle.CreateProg.property (.riscv .xor) ()
    let xorOp ← Veir.Puddle.CreateProg.operation (.riscv .xor) #[b, a] #[regType] xorProps
    let liProps ← Veir.Puddle.CreateProg.property (.riscv .li) icmpZeroImm
    let liOp ← Veir.Puddle.CreateProg.operation (.riscv .li) #[] #[regType] liProps
    let sltuProps ← Veir.Puddle.CreateProg.property (.riscv .sltu) ()
    Veir.Puddle.CreateProg.operation (.riscv .sltu)
        #[liOp.res[0]!, xorOp.res[0]!] #[regType] sltuProps
  | .slt, _ => icmpEmitCmp regType a b .slt () false
  | .sgt, _ => icmpEmitCmp regType a b .slt () true
  | .ult, _ => icmpEmitCmp regType a b .sltu () false
  | .ugt, _ => icmpEmitCmp regType a b .sltu () true
  | .sge, _ => icmpEmitCmp regType a b .slt () false (some ⟨.xori, icmpOneImm⟩)
  | .sle, _ => icmpEmitCmp regType a b .slt () true (some ⟨.xori, icmpOneImm⟩)
  | .uge, _ => icmpEmitCmp regType a b .sltu () false (some ⟨.xori, icmpOneImm⟩)
  | .ule, _ => icmpEmitCmp regType a b .sltu () true (some ⟨.xori, icmpOneImm⟩)

/--
  `llvm.icmp pred` whose lhs is `lhsWidth` bits wide once in a register (`i64`/`!llvm.ptr`,
  `i32`, or `i8`). When `zeroRhs` is set, the rhs must be the constant `0`.
-/
def lowerIcmp (pred : Data.LLVM.IntPred) (lhsWidth : Nat) (zeroRhs : Bool) :
    Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      /- support `i64`, `i32`, `i8` and `!llvm.ptr` -/
      let lhsType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
          (fun t => icmpTypeWidth? t == some lhsWidth)
      let rhsType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
          (fun t => (icmpTypeWidth? t).any (· ∈ [64, 32, 8]))
      /- The result is cast back for type consistency, so it must be an integer type. -/
      let resType ← Veir.Puddle.MatchProg.type (Attr := IntegerType)
      let lhs ← Veir.Puddle.MatchProg.value lhsType
      let rhs ← if zeroRhs then do
          let zeroOp ← Veir.Puddle.MatchProg.operation (.llvm .mlir__constant) #[] #[rhsType]
          Veir.Puddle.MatchProg.matchNative (rhsType, zeroOp.properties)
              fun (type, props) => isConstantZero type props
          pure zeroOp.res[0]!
        else
          Veir.Puddle.MatchProg.value rhsType
      let _ ← Veir.Puddle.MatchProg.root (.llvm .icmp) #[lhs, rhs] #[resType]
          (fun props => props.predicate == pred)
      return (resType, lhs, rhs))
    (fun (resType, lhs, rhs) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      let (a, b) ← icmpCastExt regType lhs rhs (icmpExtOf lhsWidth)
      let cmpOp ← icmpEmit regType pred zeroRhs a b
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[cmpOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  llvm.icmp -> riscv comparison sequence (see the arms above).

  Peephole for `eq`/`ne`: when the rhs is a constant `0`, the `xor` is unnecessary and the
  comparison is against the left register directly (`seqz`/`snez`). These patterns come first, so
  they take priority over the generic arms. Canonicalization runs before isel and moves the
  constant to the rhs, so we only check that side.
  LLVM: `Pat<(riscv_seteq GPR:$rs1), (SLTIU GPR:$rs1, 1)>` and
  `Pat<(riscv_setne GPR:$rs1), (SLTU (XLenVT X0), GPR:$rs1)>`.
  https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1649
-/
def icmp : Array (Puddle.CompiledPattern OpCode) :=
  let widths := #[64, 32, 8]
  let preds : Array Data.LLVM.IntPred :=
    #[.eq, .ne, .slt, .sgt, .ult, .ugt, .sge, .sle, .uge, .ule]
  let peepholes := widths.flatMap fun w =>
    #[Data.LLVM.IntPred.eq, .ne].map fun pred => lowerIcmp pred w true
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
  byte types, and the result is strictly narrower than the operand.

  The operand is held in a 64-bit register, so an operand wider than 64 bits would lose bits in
  the round trip. Every narrower pair of widths is sound (see `trunc_refinement_le64`), including
  odd ones such as `i1`: the result's upper register bits are whatever the operand left there,
  and `reconcile-cast` zero-extends the value wherever it is used as a register again.
-/
def isLegalTrunc (opType resType : TypeAttr) : Bool :=
  let shouldTruncate := match opType.val, resType.val with
    | .integerType _, .integerType _ => true
    | .byteType _, .byteType _ => true
    | _, _ => false
  match getIntByteTypeBitwidth opType, getIntByteTypeBitwidth resType with
  | some opBw, some resBw => shouldTruncate && resBw < opBw && opBw ≤ 64
  | _, _ => false

/--
  Shared shape of the lowerings of single-operand LLVM ops that are no-ops on registers
  (`trunc`/`bitcast`): when `legal` accepts the operand and result types, cast the operand to a
  register, then cast the register to the result type.
-/
def lowerRegCast (llvmOp : Llvm) (legal : TypeAttr → TypeAttr → Bool) : Veir.Puddle.Pattern OpCode :=
  Veir.Puddle.Pattern.Builder
    (do
      let opType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
      let resType ← Veir.Puddle.MatchProg.type (Attr := TypeAttr)
      let x ← Veir.Puddle.MatchProg.value opType
      let _ ← Veir.Puddle.MatchProg.root (.llvm llvmOp) #[x] #[resType]
      Veir.Puddle.MatchProg.matchNative (opType, resType)
          fun (opType, resType) => legal opType resType
      return (resType, x))
    (fun (resType, x) => do
      let regType ← Veir.Puddle.CreateProg.type (RegisterType.mk none)
      /- First, cast the operand to registers -/
      let castProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[x] #[regType] castProps
      /- Then, cast register to expected output type. -/
      let castBackProps ← Veir.Puddle.CreateProg.property (.builtin .unrealized_conversion_cast) ()
      let castBackOp ← Veir.Puddle.CreateProg.operation (.builtin .unrealized_conversion_cast)
          #[castOp.res[0]!] #[resType] castBackProps
      return castBackOp)
    (fun castBackOp => castBackOp)

/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!riscv.reg) : iY
  where `iY`'s width is smaller than `iX`'s (see `isLegalTrunc`).
  Also accepts the byte type.
-/
def trunc_pattern : Veir.Puddle.Pattern OpCode := lowerRegCast .trunc isLegalTrunc

/--
  llvm.trunc -> builtin_unrealized_conversion_cast (see `trunc_pattern`).
-/
def trunc : Puddle.CompiledPattern OpCode := trunc_pattern.compile

/-- llvm.shl -> riscv.sll -/
def shl64 : Puddle.CompiledPattern OpCode := shl64_pattern.compile

/-- llvm.shl -> riscv.sllw -/
def shl32 : Puddle.CompiledPattern OpCode := shl32_pattern.compile

/-- llvm.lshr -> riscv.srl -/
def lshr64 : Puddle.CompiledPattern OpCode := lshr64_pattern.compile

/-- llvm.lshr -> riscv.srlw -/
def lshr32 : Puddle.CompiledPattern OpCode := lshr32_pattern.compile

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

/-- Whether `llvm.bitcast` from `opType` to `resType` is lowered: both are integer, byte, or
    pointer types of width 8, 16, 32, or 64, and it is not a `byte -> ptr` bitcast. -/
def isLegalBitcast (opType resType : TypeAttr) : Bool :=
  checkBitcastType opType && checkBitcastType resType && !isBitcastByteToPtr opType resType &&
    match Attribute.bitwidthOfType opType, Attribute.bitwidthOfType resType with
    | some opBw, some resBw => opBw ∈ [8, 16, 32, 64] && resBw ∈ [8, 16, 32, 64]
    | _, _ => false

/--
  llvm.bitcast t1 %x to t2 -> builtin_unrealized_conversion_cast
  Integers, bytes, and pointers are all lowered to !riscv.reg, making this basically a no-op.
  The `byte -> ptr` case is excluded (see `isLegalBitcast`).
-/
def bitcast_pattern : Veir.Puddle.Pattern OpCode := lowerRegCast .bitcast isLegalBitcast

/-- llvm.bitcast -> builtin_unrealized_conversion_cast (see `bitcast_pattern`). -/
def bitcast : Puddle.CompiledPattern OpCode := bitcast_pattern.compile

/--
  Lower LLVM lifetime instructions to nothing. This is a refinement that we can
  revisit later if we want to perform certain stack slot optimizations.
-/
def lifetime_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  match op.getOpType! ctx.raw with
  | .llvm .intr__lifetime__start | .llvm .intr__lifetime__end =>
    some (ctx, some (#[], #[]))
  | _ => some (ctx, none)

/-- Erase `llvm.intr.lifetime.start` and `llvm.intr.lifetime.end`. -/
def lifetime := RewritePattern.fromLocalRewrite lifetime_local

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

/--
  Split a load/store address into a base register operand and a signed 12-bit
  immediate offset, mirroring the `isBaseWithConstantOffset` case of LLVM's
  [`RISCVDAGToDAGISel::SelectAddrRegImm`](https://github.com/llvm/llvm-project/blob/llvmorg-22.1.8/llvm/lib/Target/RISCV/RISCVISelDAGToDAG.cpp#L3175-L3206).
-/
def selectAddrRegImm (ptr : ValuePtr) (ctx : IRContext OpCode) : ValuePtr × Int :=
  let folded : Option (ValuePtr × Int) := do
    let gepOp ← ptr.definingOp?
    let (base, idx, properties) ← matchGetelementptr gepOp ctx
    /- A single dynamic index with no trailing constant indices, as in `getelementptr_local`. -/
    guard (properties.rawConstantIndices.values = #[(-2147483648 : Int)])
    let .integerType itype := (idx.getType! ctx).val | none
    guard (itype.bitwidth = 64)
    let c ← matchConstantIntVal idx ctx
    let scale ← DataLayout.riscv64.getTypeAllocSize properties.elem_type.val
    let offset := c * (scale : Int)
    guard (-2048 ≤ offset ∧ offset ≤ 2047)
    return (base, offset)
  folded.getD (ptr, 0)

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

/-- llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8) -/
def load_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (ptr, llvmProps) := matchLoad op ctx.raw | return (ctx, none)
  /- support `i64`, `i32`, `i16`, `i8` and `!llvm.ptr` (the loaded value type) -/
  let type := ((op.getResult 0).get! ctx.raw).type
  let some width := memAccessWidth? type | return (ctx, none)
  /- Split the address into a base register and a signed 12-bit offset. -/
  let (base, offset) := selectAddrRegImm ptr ctx.raw
  /- cast base (!llvm.ptr) -> register -/
  let (ctx, pcastOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[base]
      #[] #[] () none
  /- Volatility carries over from the `llvm.load`: the riscv op encodes the same, but the
     flag keeps later passes from deleting or duplicating the access. -/
  let immProps := RISCVMemProperties.mk (BitVec.ofInt 64 offset) llvmProps.volatile_
  let (ctx, ldOp) ← createLoadLocal ctx width (pcastOp.getResult 0) immProps
  let (ctx, castOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[type] #[ldOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[pcastOp, ldOp, castOp], #[castOp.getResult 0]))

/-- llvm.load -> riscv.ld (i64, ptr) / riscv.lw (i32) / riscv.lh (i16) / riscv.lb (i8) -/
def load (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite load_local rewriter op opInBounds

/-- llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8) -/
def store_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (arg, ptr, llvmProps) := matchStore op ctx.raw | return (ctx, none)
  /- support `i64`, `i32`, `i16`, `i8` and `!llvm.ptr` (the stored value type) -/
  let type := arg.getType! ctx.raw
  let some width := memAccessWidth? type | return (ctx, none)
  /- Split the address into a base register and a signed 12-bit offset. -/
  let (base, offset) := selectAddrRegImm ptr ctx.raw
  /- cast base (!llvm.ptr) -> register -/
  let (ctx, pcastOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[base]
      #[] #[] () none
  /- cast value (i64/i32/i16/i8/ptr) -> register -/
  let (ctx, valcastOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[arg]
      #[] #[] () none
  /- The store writes the low `width` bytes of the value register. Volatility carries over
     from the `llvm.store`, as in `load_local`. -/
  let immProps := RISCVMemProperties.mk (BitVec.ofInt 64 offset) llvmProps.volatile_
  let (ctx, sdOp) ← createStoreLocal ctx width (valcastOp.getResult 0) (pcastOp.getResult 0) immProps
  some (ctx, some (#[pcastOp, valcastOp, sdOp], #[]))

/-- llvm.store -> riscv.sd (i64, ptr) / riscv.sw (i32) / riscv.sh (i16) / riscv.sb (i8) -/
def store (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite store_local rewriter op opInBounds

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the allocation size (ABI stride) of the element type.
-/
def getelementptr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (ptr, idx, properties) := matchGetelementptr op ctx.raw | return (ctx, none)
  /- Bail unless it's a single dynamic index with no trailing constant indices. -/
  if properties.rawConstantIndices.values ≠ #[(-2147483648 : Int)] then return (ctx, none)
  /- The index must be `i64`. -/
  let .integerType itype := (idx.getType! ctx.raw).val | return (ctx, none)
  if itype.bitwidth ≠ 64 then return (ctx, none)
  let some scale := DataLayout.riscv64.getTypeAllocSize properties.elem_type.val
    | return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let (ctx, pcastOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[ptr]
      #[] #[] () none
  let (ctx, icastOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[idx]
      #[] #[] () none
  let pReg := pcastOp.getResult 0
  let iReg := icastOp.getResult 0
  let (ctx, gepOps, retOp) ← match scale with
    | 1 =>
      /- ptr + idx -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx Riscv.add #[RegisterType.mk] #[pReg, iReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | 2 =>
      /- (idx << 1) + ptr -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx Riscv.sh1add #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | 4 =>
      /- (idx << 2) + ptr -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx Riscv.sh2add #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | 8 =>
      /- (idx << 3) + ptr -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx Riscv.sh3add #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | _ =>
      /- `0 < scale` excludes zero-sized element types (`i0`, `!llvm.array<0 x _>`), for which
         `scale &&& (scale - 1) == 0` also holds but `Nat.log2 0 = 0` would emit `idx << 0`, i.e.
         `ptr + idx` rather than `ptr`. `Nat.log2 scale < 64` excludes element sizes of `2^64` and
         beyond, whose shift amount does not fit the 6-bit immediate. Both fall through to the
         `li`/`mul` form below, which truncates modulo `2^64` exactly as the source does. -/
      if 0 < scale ∧ scale &&& (scale - 1) = 0 ∧ Nat.log2 scale < 64 then
        /- scale is a power of two: ptr + (idx << log2 scale) -/
        let k := RISCVImmediateProperties.mk (BitVec.ofInt 64 (Nat.log2 scale))
        let (ctx, slliOp) ← WfRewriter.createOp! ctx Riscv.slli #[RegisterType.mk] #[iReg]
          #[] #[] k none
        let (ctx, addOp) ← WfRewriter.createOp! ctx Riscv.add #[RegisterType.mk] #[pReg, slliOp.getResult 0]
          #[] #[] () none
        pure (ctx, #[slliOp, addOp], addOp)
      else
        /- arbitrary scale: ptr + idx * scale -/
        let s := RISCVImmediateProperties.mk (BitVec.ofInt 64 scale)
        let (ctx, liOp) ← WfRewriter.createOp! ctx Riscv.li #[RegisterType.mk] #[]
          #[] #[] s none
        let (ctx, mulOp) ← WfRewriter.createOp! ctx Riscv.mul #[RegisterType.mk] #[iReg, liOp.getResult 0]
          #[] #[] () none
        let (ctx, addOp) ← WfRewriter.createOp! ctx Riscv.add #[RegisterType.mk] #[pReg, mulOp.getResult 0]
          #[] #[] () none
        pure (ctx, #[liOp, mulOp, addOp], addOp)
  /- Cast the resulting register back to `!llvm.ptr`. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[type] #[retOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[pcastOp, icastOp] ++ gepOps ++ #[castOp], #[castOp.getResult 0]))

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the allocation size (ABI stride) of the element type.
-/
def getelementptr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite getelementptr_local rewriter op opInBounds

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
  `select c t 0` -> `riscv.czeroeqz t c`.
-/
def selectCzeroeqz_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tval, fval) := matchSelect op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some _ := matchConstantZero fval ctx.raw | return (ctx, none)
  let (ctx, tCastOp) ← castToRegLocal ctx tval
  let (ctx, condCastOp) ← castToRegLocal ctx cond
  let (ctx, czOp) ← WfRewriter.createOp! ctx Riscv.czeroeqz #[RegisterType.mk] #[tCastOp.getResult 0, condCastOp.getResult 0]
      #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (czOp.getResult 0)
  some (ctx, some (#[tCastOp, condCastOp, czOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `select c t 0` -> `riscv.czeroeqz t c`.
-/
def selectCzeroeqz (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite selectCzeroeqz_local rewriter op opInBounds

/--
  `select c 0 f` -> `riscv.czeronez f c`.
-/
def selectCzeronez_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tval, fval) := matchSelect op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some _ := matchConstantZero tval ctx.raw | return (ctx, none)
  let (ctx, fCastOp) ← castToRegLocal ctx fval
  let (ctx, condCastOp) ← castToRegLocal ctx cond
  let (ctx, czOp) ← WfRewriter.createOp! ctx Riscv.czeronez #[RegisterType.mk] #[fCastOp.getResult 0, condCastOp.getResult 0]
      #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (czOp.getResult 0)
  some (ctx, some (#[fCastOp, condCastOp, czOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `select c 0 f` -> `riscv.czeronez f c`.
-/
def selectCzeronez (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite selectCzeronez_local rewriter op opInBounds

/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (cond, tval, fval) := matchSelect op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 ∧ t.bitwidth ≠ 1 then return (ctx, none)
  let (ctx, tCastOp) ← castToRegLocal ctx tval
  let (ctx, fCastOp) ← castToRegLocal ctx fval
  let (ctx, condCastOp) ← castToRegLocal ctx cond
  let (ctx, eqzOp) ← WfRewriter.createOp! ctx Riscv.czeroeqz #[RegisterType.mk] #[tCastOp.getResult 0, condCastOp.getResult 0]
      #[] #[] () none
  let (ctx, nezOp) ← WfRewriter.createOp! ctx Riscv.czeronez #[RegisterType.mk] #[fCastOp.getResult 0, condCastOp.getResult 0]
      #[] #[] () none
  let (ctx, orOp) ← WfRewriter.createOp! ctx Riscv.or #[RegisterType.mk]
      #[eqzOp.getResult 0, nezOp.getResult 0]
      #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
  some (ctx, some (#[tCastOp, fCastOp, condCastOp, eqzOp, nezOp, orOp, castBackOp], #[castBackOp.getResult 0]))

/--
  General branchless select:
  `select c t f` -> `or (czero.eqz t c) (czero.nez f c)`.
-/
def selectGeneral (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite selectGeneral_local rewriter op opInBounds

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

def mkRISCVImm (value : Int) : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (BitVec.ofInt 64 value)

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

def signedSatSelectLocal (ctx : WfIRContext OpCode) (op : OperationPtr)
    (wrapped overflow sat : ValuePtr) :
    Option (WfIRContext OpCode × Array OperationPtr × Array ValuePtr) := do
  let (ctx, wrappedOrZero) ← WfRewriter.createOp! ctx Riscv.czeronez #[RegisterType.mk]
      #[wrapped, overflow] #[] #[] () none
  let (ctx, satOrZero) ← WfRewriter.createOp! ctx Riscv.czeroeqz #[RegisterType.mk]
      #[sat, overflow] #[] #[] () none
  let (ctx, selectOp) ← WfRewriter.createOp! ctx Riscv.or #[RegisterType.mk]
      #[satOrZero.getResult 0, wrappedOrZero.getResult 0] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (selectOp.getResult 0)
  return (ctx, #[wrappedOrZero, satOrZero, selectOp, castBackOp], #[castBackOp.getResult 0])

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchSaddSat op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let lReg := lCastOp.getResult 0
  let rReg := rCastOp.getResult 0
  let (ctx, minusOne) ← createRISCVImmLocal ctx .li rfl #[] (-1)
  let (ctx, sum) ← createRISCVUnitLocal ctx .add rfl #[lReg, rReg]
  let (ctx, rhsSign) ← createRISCVImmLocal ctx .srli rfl #[rReg] 63
  let (ctx, carryLike) ← createRISCVUnitLocal ctx .slt rfl #[sum.getResult 0, lReg]
  let (ctx, sumSign) ← createRISCVImmLocal ctx .srai rfl #[sum.getResult 0] 63
  let (ctx, intMin) ← createRISCVImmLocal ctx .slli rfl #[minusOne.getResult 0] 63
  let (ctx, overflow) ← createRISCVUnitLocal ctx .xor rfl #[rhsSign.getResult 0, carryLike.getResult 0]
  let (ctx, sat) ← createRISCVUnitLocal ctx .xor rfl #[sumSign.getResult 0, intMin.getResult 0]
  let (ctx, selectOps, newValues) ←
    signedSatSelectLocal ctx op (sum.getResult 0) (overflow.getResult 0) (sat.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, minusOne, sum, rhsSign, carryLike, sumSign, intMin,
      overflow, sat] ++ selectOps, newValues))

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite saddSat_local rewriter op opInBounds

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchSsubSat op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let lReg := lCastOp.getResult 0
  let rReg := rCastOp.getResult 0
  let (ctx, minusOne) ← createRISCVImmLocal ctx .li rfl #[] (-1)
  let (ctx, diff) ← createRISCVUnitLocal ctx .sub rfl #[lReg, rReg]
  let (ctx, cmp) ← createRISCVUnitLocal ctx .slt rfl #[lReg, rReg]
  let (ctx, diffSignBit) ← createRISCVImmLocal ctx .srli rfl #[diff.getResult 0] 63
  let (ctx, diffSign) ← createRISCVImmLocal ctx .srai rfl #[diff.getResult 0] 63
  let (ctx, intMin) ← createRISCVImmLocal ctx .slli rfl #[minusOne.getResult 0] 63
  let (ctx, overflow) ← createRISCVUnitLocal ctx .xor rfl #[cmp.getResult 0, diffSignBit.getResult 0]
  let (ctx, sat) ← createRISCVUnitLocal ctx .xor rfl #[diffSign.getResult 0, intMin.getResult 0]
  let (ctx, selectOps, newValues) ←
    signedSatSelectLocal ctx op (diff.getResult 0) (overflow.getResult 0) (sat.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, minusOne, diff, cmp, diffSignBit, diffSign, intMin,
      overflow, sat] ++ selectOps, newValues))

/-- llvm.intr.ssub.sat.i64 -> LLVM's RV64+Zicond signed saturating-sub sequence.
    Wrapped `sub` + SSUBO overflow `(lhs <s rhs) ^ (diff >>u 63)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13082
    `expandSADDSUBO` sub branch; sat endpoint `(diff >>s 63) ^ INT_MIN` at 12554). -/
def ssubSat (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ssubSat_local rewriter op opInBounds

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchUaddSat op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let lReg := lCastOp.getResult 0
  let rReg := rCastOp.getResult 0
  let (ctx, notRhs) ← createRISCVImmLocal ctx .xori rfl #[rReg] (-1)
  let (ctx, minuOp) ← createRISCVUnitLocal ctx .minu rfl #[lReg, notRhs.getResult 0]
  let (ctx, addOp) ← createRISCVUnitLocal ctx .add rfl #[minuOp.getResult 0, rReg]
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (addOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, notRhs, minuOp, addOp, castBackOp],
      #[castBackOp.getResult 0]))

/-- llvm.intr.uadd.sat.i64 -> not rhs; minu lhs, not-rhs; add rhs.
    `uadd.sat(a,b) -> umin(a, ~b) + b` (TargetLowering.cpp:12462
    `expandAddSubSat`, UADDSAT/UMIN idiom). -/
def uaddSat (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite uaddSat_local rewriter op opInBounds

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchUsubSat op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let lReg := lCastOp.getResult 0
  let rReg := rCastOp.getResult 0
  let (ctx, maxuOp) ← createRISCVUnitLocal ctx .maxu rfl #[lReg, rReg]
  let (ctx, subOp) ← createRISCVUnitLocal ctx .sub rfl #[maxuOp.getResult 0, rReg]
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (subOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, maxuOp, subOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.usub.sat.i64 -> maxu lhs, rhs; sub rhs.
    `usub.sat(a,b) -> umax(a, b) - b` (TargetLowering.cpp:12442
    `expandAddSubSat`, USUBSAT/UMAX idiom). -/
def usubSat (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite usubSat_local rewriter op opInBounds

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchSshlSat op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let lReg := lCastOp.getResult 0
  let rReg := rCastOp.getResult 0
  let (ctx, shifted) ← createRISCVUnitLocal ctx .sll rfl #[lReg, rReg]
  let (ctx, minusOne) ← createRISCVImmLocal ctx .li rfl #[] (-1)
  let (ctx, unshifted) ← createRISCVUnitLocal ctx .sra rfl #[shifted.getResult 0, rReg]
  let (ctx, sign) ← createRISCVImmLocal ctx .srai rfl #[lReg] 63
  let (ctx, intMax) ← createRISCVImmLocal ctx .srli rfl #[minusOne.getResult 0] 1
  let (ctx, overflow) ← createRISCVUnitLocal ctx .xor rfl #[lReg, unshifted.getResult 0]
  let (ctx, sat) ← createRISCVUnitLocal ctx .xor rfl #[sign.getResult 0, intMax.getResult 0]
  let (ctx, selectOps, newValues) ←
    signedSatSelectLocal ctx op (shifted.getResult 0) (overflow.getResult 0) (sat.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, shifted, minusOne, unshifted, sign, intMax,
      overflow, sat] ++ selectOps, newValues))

/-- llvm.intr.sshl.sat.i64 -> LLVM's RV64+Zicond signed saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>s rhs`, saturate to
    `select(lhs<0, INT_MIN, INT_MAX)` folded to `(lhs >>s 63) ^ INT_MAX`
    (TargetLowering.cpp:12598 `expandShlSat`, signed branch at 12626-12632). -/
def sshlSat (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sshlSat_local rewriter op opInBounds

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchUshlSat op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let lReg := lCastOp.getResult 0
  let rReg := rCastOp.getResult 0
  let (ctx, shifted) ← createRISCVUnitLocal ctx .sll rfl #[lReg, rReg]
  let (ctx, unshifted) ← createRISCVUnitLocal ctx .srl rfl #[shifted.getResult 0, rReg]
  let (ctx, lostBits) ← createRISCVUnitLocal ctx .xor rfl #[lReg, unshifted.getResult 0]
  let (ctx, noOverflow) ← createRISCVImmLocal ctx .sltiu rfl #[lostBits.getResult 0] 1
  let (ctx, overflowMask) ← createRISCVImmLocal ctx .addi rfl #[noOverflow.getResult 0] (-1)
  let (ctx, orOp) ← createRISCVUnitLocal ctx .or rfl #[overflowMask.getResult 0, shifted.getResult 0]
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, shifted, unshifted, lostBits, noOverflow, overflowMask,
      orOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.ushl.sat.i64 -> LLVM's RV64 unsigned saturating-shl sequence.
    `overflow = lhs != (lhs << rhs) >>u rhs`, saturate to all-ones;
    the `select(overflow, ~0, shifted)` becomes the `sltiu`/`addi`/`or`
    mask idiom (TargetLowering.cpp:12598 `expandShlSat`, unsigned branch
    at 12630-12633). -/
def ushlSat (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ushlSat_local rewriter op opInBounds

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max`.
    LLVM's RV64+Zbb lowering (`neg a1, a0; max a0, a0, a1`). The `neg` wraps
    `intMin` back to `intMin`, so this is correct for both the
    `is_int_min_poison` and non-poison forms of the intrinsic. -/
def abs_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some val := matchAbs op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx val
  let xReg := castOp.getResult 0
  let (ctx, negOp) ← createRISCVUnitLocal ctx .neg rfl #[xReg]
  let (ctx, maxOp) ← createRISCVUnitLocal ctx .max rfl #[xReg, negOp.getResult 0]
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (maxOp.getResult 0)
  some (ctx, some (#[castOp, negOp, maxOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.abs.i64 -> `max(x, -x)` via Zbb `neg`/`max`.
    LLVM's RV64+Zbb lowering (`neg a1, a0; max a0, a0, a1`). The `neg` wraps
    `intMin` back to `intMin`, so this is correct for both the
    `is_int_min_poison` and non-poison forms of the intrinsic. -/
def abs (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite abs_local rewriter op opInBounds

/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror (riscv.rorw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr64 : Puddle.CompiledPattern OpCode := fshr64_pattern.compile

def fshr32 : Puddle.CompiledPattern OpCode := fshr32_pattern.compile
/-- llvm.intr.fshr with identical data operands and a constant shift amount is a
    constant rotate-right: -> riscv.rori (mirrors `PatGprImm<rotr, RORI>`). -/
def fshrConst_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshr op ctx.raw | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let some amtAttr := matchConstantIntVal amt ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  if t.bitwidth = 32 then
    let sh : Int := ((amtAttr % 32) + 32) % 32
    let imm := RISCVImmediateProperties.mk (BitVec.ofInt 64 sh)
    let (ctx, roriOp) ← WfRewriter.createOp! ctx Riscv.roriw #[RegisterType.mk] #[valCastOp.getResult 0]
        #[] #[] imm none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
    some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))
  else
    /- The funnel-shift amount is taken modulo the bit width. -/
    let sh : Int := ((amtAttr % 64) + 64) % 64
    let imm := RISCVImmediateProperties.mk (BitVec.ofInt 64 sh)
    let (ctx, roriOp) ← WfRewriter.createOp! ctx Riscv.rori #[RegisterType.mk] #[valCastOp.getResult 0]
        #[] #[] imm none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
    some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.fshr with identical data operands and a constant shift amount is a
    constant rotate-right: -> riscv.rori (mirrors `PatGprImm<rotr, RORI>`). -/
def fshrConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite fshrConst_local rewriter op opInBounds

/-- llvm.intr.fshl with identical data operands and a constant shift amount is a
    constant rotate-left. There is no `roli`, so (like LLVM) it lowers to
    `riscv.rori` with the negated immediate `(64 - amt) mod 64`. -/
def fshlConst_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshl op ctx.raw | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let some amtAttr := matchConstantIntVal amt ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  if t.bitwidth = 32 then
    /- rotate-left by `sh` == rotate-right by `32 - sh` (mod 32). -/
    let sh : Int := ((amtAttr % 32) + 32) % 32
    let imm : Int := (32 - sh) % 32
    let immProps := RISCVImmediateProperties.mk (BitVec.ofInt 64 imm)
    let (ctx, roriOp) ← WfRewriter.createOp! ctx Riscv.roriw #[RegisterType.mk] #[valCastOp.getResult 0]
        #[] #[] immProps none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
    some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))
  else
    /- rotate-left by `sh` == rotate-right by `64 - sh` (mod 64). -/
    let sh : Int := ((amtAttr % 64) + 64) % 64
    let imm : Int := (64 - sh) % 64
    let immProps := RISCVImmediateProperties.mk (BitVec.ofInt 64 imm)
    let (ctx, roriOp) ← WfRewriter.createOp! ctx Riscv.rori #[RegisterType.mk] #[valCastOp.getResult 0]
        #[] #[] immProps none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
    some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.fshl with identical data operands and a constant shift amount is a
    constant rotate-left. There is no `roli`, so (like LLVM) it lowers to
    `riscv.rori` with the negated immediate `(64 - amt) mod 64`. -/
def fshlConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite fshlConst_local rewriter op opInBounds

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
def fshlGeneral_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshl op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx a
  let (ctx, yCastOp) ← castToRegLocal ctx b
  let (ctx, zCastOp) ← castToRegLocal ctx amt
  /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
  let notImm := RISCVImmediateProperties.mk (-1#64)
  let (ctx, notzOp) ← WfRewriter.createOp! ctx Riscv.xori #[RegisterType.mk] #[zCastOp.getResult 0]
      #[] #[] notImm none
  let oneImm := RISCVImmediateProperties.mk 1#64
  /- shx = x << z ; shy = (y >> 1) >> ~z ; result = shx | shy. The i32 form uses
     the `w` shifts (only the low 32 bits of the `or` are observed). -/
  if t.bitwidth = 32 then
    let (ctx, shxOp) ← WfRewriter.createOp! ctx Riscv.sllw #[RegisterType.mk] #[xCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, y1Op) ← WfRewriter.createOp! ctx Riscv.srliw #[RegisterType.mk] #[yCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx Riscv.srlw #[RegisterType.mk] #[y1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx Riscv.or #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
    some (ctx, some (#[xCastOp, yCastOp, zCastOp, notzOp, shxOp, y1Op, shyOp, orOp, castBackOp],
      #[castBackOp.getResult 0]))
  else
    let (ctx, shxOp) ← WfRewriter.createOp! ctx Riscv.sll #[RegisterType.mk] #[xCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, y1Op) ← WfRewriter.createOp! ctx Riscv.srli #[RegisterType.mk] #[yCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx Riscv.srl #[RegisterType.mk] #[y1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx Riscv.or #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
    some (ctx, some (#[xCastOp, yCastOp, zCastOp, notzOp, shxOp, y1Op, shyOp, orOp, castBackOp],
      #[castBackOp.getResult 0]))

/-- General `llvm.intr.fshl` -> shift/or expansion (see `fshlGeneral_local`). -/
def fshlGeneral (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite fshlGeneral_local rewriter op opInBounds

/-- General `llvm.intr.fshr x y z` -> `((x << 1) << ~z) | (y >> z)` (see the
    section comment). Handles i64 and i32; the i32 form uses the `w` shifts. -/
def fshrGeneral_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshr op ctx.raw | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx a
  let (ctx, yCastOp) ← castToRegLocal ctx b
  let (ctx, zCastOp) ← castToRegLocal ctx amt
  /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
  let notImm := RISCVImmediateProperties.mk (-1#64)
  let (ctx, notzOp) ← WfRewriter.createOp! ctx Riscv.xori #[RegisterType.mk] #[zCastOp.getResult 0]
      #[] #[] notImm none
  let oneImm := RISCVImmediateProperties.mk 1#64
  /- shx = (x << 1) << ~z ; shy = y >> z ; result = shx | shy. The i32 form uses
     the `w` shifts (only the low 32 bits of the `or` are observed). -/
  if t.bitwidth = 32 then
    let (ctx, x1Op) ← WfRewriter.createOp! ctx Riscv.slliw #[RegisterType.mk] #[xCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shxOp) ← WfRewriter.createOp! ctx Riscv.sllw #[RegisterType.mk] #[x1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx Riscv.srlw #[RegisterType.mk] #[yCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx Riscv.or #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
    some (ctx, some (#[xCastOp, yCastOp, zCastOp, notzOp, x1Op, shxOp, shyOp, orOp, castBackOp],
      #[castBackOp.getResult 0]))
  else
    let (ctx, x1Op) ← WfRewriter.createOp! ctx Riscv.slli #[RegisterType.mk] #[xCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shxOp) ← WfRewriter.createOp! ctx Riscv.sll #[RegisterType.mk] #[x1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx Riscv.srl #[RegisterType.mk] #[yCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx Riscv.or #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
    some (ctx, some (#[xCastOp, yCastOp, zCastOp, notzOp, x1Op, shxOp, shyOp, orOp, castBackOp],
      #[castBackOp.getResult 0]))

/-- General `llvm.intr.fshr` -> shift/or expansion (see `fshrGeneral_local`). -/
def fshrGeneral (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite fshrGeneral_local rewriter op opInBounds


/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some _ := matchPoison op ctx.raw | return (ctx, none)
  let imm := RISCVImmediateProperties.mk 0#64
  let (ctx, liOp) ← WfRewriter.createOp! ctx Riscv.li #[RegisterType.mk] #[]
      #[] #[] imm none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (liOp.getResult 0)
  some (ctx, some (#[liOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.mlir.poison -> riscv.li 0 -/
def poisonConst (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite poisonConst_local rewriter op opInBounds

/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some operand := matchFreeze op ctx.raw | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType retType := type.val | return (ctx, none)
  if (opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32) ∨ (retType.bitwidth ≠ 64 ∧ retType.bitwidth ≠ 32) then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[RegisterType.mk] #[operand]
      #[] #[] () none
  /- Then, cast register to expected output width. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx Builtin.unrealized_conversion_cast #[type] #[opCastOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, castOp], #[castOp.getResult 0]))

/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite freeze_local rewriter op opInBounds

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
  let early := RewritePattern.GreedyRewritePattern #[lifetime, alloca, memIntrinsic, load, store]
  let ctx ← match RewritePattern.applyInContext early ctx with
  | none => throw "Error while applying early memory-lowering patterns"
  | some ctx => pure ctx
  /- Main loop: the existing per-op lowerings. -/
  let pattern := RewritePattern.GreedyRewritePattern <|
    #[selectCzeroeqz, selectCzeronez, selectGeneral,
    ctlz32.run, ctlz64.run, cttz32.run, cttz64.run, ctpop32.run, ctpop64.run, bswap64.run, bswap32.run, bitreverse64.run, bitreverse32.run,
    constant.run, addressof, add32.run, add64.run, and.run, ashr64.run, ashr32.run, ashr8.run] ++
    icmp.map (·.run) ++ #[or.run, xor32.run, xor64.run, mul32.run, mul64.run,
    sdiv32.run, sdiv64.run, udiv32.run, udiv64.run, srem32.run, srem64.run, urem32.run, urem64.run,
    sext32.run, sext16.run, sext8.run, zext32.run, zext16.run, zext8.run, trunc.run, shl64.run, shl32.run, lshr64.run, lshr32.run,
    sub64.run, sub32.run, bitcast.run, load, getelementptr, store,
    smax64.run, smax32.run, smin64.run, smin32.run, umax.run, umin.run, saddSat, ssubSat, uaddSat, usubSat, sshlSat, ushlSat, abs,
    fshlConst, fshrConst, fshl64.run, fshl32.run, fshr64.run, fshr32.run, fshlGeneral, fshrGeneral, poisonConst, freeze]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying main instruction-selection patterns"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := fun _ => ISelPass.impl }
