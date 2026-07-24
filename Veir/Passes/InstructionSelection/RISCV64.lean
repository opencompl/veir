module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching.LLVM.Basic
import Veir.Passes.InstructionSelection.Common

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
  Shared shape of the unary RISC-V lowerings (`ctlz`/`cttz`/`ctpop`): match a single-operand
  LLVM op whose operand has integer type `i64` or `i32`, cast the operand to a register, apply
  `op64` (or its `W` variant `op32` for `i32`), and cast the result back to the source type.
-/
def lowerUnaryWLocal {P : Type}
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × P))
    (op64 op32 : Riscv)
    (props64 : propertiesOf (.riscv op64)) (props32 : propertiesOf (.riscv op32))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := match? op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  let (ctx, retOp) ←
    if opType.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv op32) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] props32 none
    else
      WfRewriter.createOp! ctx (.riscv op64) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] props64 none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[castOp, retOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the integer-extension lowerings (`sext`/`zext`): match a single-operand LLVM
  extension op whose operand has integer type `i8`, `i16`, or `i32` (see `isLegalExtOpWidth`) and
  whose result is a strictly wider integer type of width at most 64 (a 64-bit register cannot
  represent wider results, so e.g. `sext i8 to i128` is left unselected), cast the operand to a
  register, apply the byte/halfword/word extension op matching the *operand* width (`op8`/`op16`/
  `op32`), and cast the result back to the result type.
-/
def lowerExtLocal {P : Type}
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × P))
    (op8 op16 op32 : Riscv)
    (props8 : propertiesOf (.riscv op8)) (props16 : propertiesOf (.riscv op16))
    (props32 : propertiesOf (.riscv op32))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := match? op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if ¬ isLegalExtOpWidth opType.bitwidth then return (ctx, none)
  let .integerType retType := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if retType.bitwidth ≤ opType.bitwidth ∨ 64 < retType.bitwidth then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  let (ctx, retOp) ←
    if opType.bitwidth = 8 then
      WfRewriter.createOp! ctx (.riscv op8) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] props8 none
    else if opType.bitwidth = 16 then
      WfRewriter.createOp! ctx (.riscv op16) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] props16 none
    else
      WfRewriter.createOp! ctx (.riscv op32) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] props32 none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[castOp, retOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the binary RISC-V lowerings (`add`/`sub`/`mul`/`sdiv`/…): match a two-operand
  LLVM op whose operands have integer type `i64` or `i32`, cast both operands to registers, apply
  `op64` (or its `W` variant `op32` for `i32`) to the two registers, and cast the result back to
  the source type. Ops without a `W` variant (e.g. `xor`) pass the same opcode twice.
-/
def lowerBinaryWLocal {P : Type}
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × P))
    (op64 op32 : Riscv)
    (props64 : propertiesOf (.riscv op64)) (props32 : propertiesOf (.riscv op32))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := match? op ctx | return (ctx, none)
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lcastOp) ← castToRegLocal ctx lhs
  let (ctx, rcastOp) ← castToRegLocal ctx rhs
  let (ctx, retOp) ←
    if ltype.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv op32) #[RegisterType.mk]
          #[lcastOp.getResult 0, rcastOp.getResult 0] #[] #[] props32 none
    else
      WfRewriter.createOp! ctx (.riscv op64) #[RegisterType.mk]
          #[lcastOp.getResult 0, rcastOp.getResult 0] #[] #[] props64 none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[lcastOp, rcastOp, retOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the binary RISC-V lowerings that accept both integer and byte values (`shl`/`lshr`).
-/
def lowerByteBinaryWLocal {P : Type}
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × P))
    (op64 op32 : Riscv)
    (props64 : propertiesOf (.riscv op64)) (props32 : propertiesOf (.riscv op32))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := match? op ctx | return (ctx, none)
  let ltype := (lhs.getType! ctx.raw)
  let some bw := getIntByteTypeBitwidth ltype | return (ctx, none)
  if bw ≠ 64 ∧ bw ≠ 32 then return (ctx, none)
  let (ctx, lcastOp) ← castToRegLocal ctx lhs
  let (ctx, rcastOp) ← castToRegLocal ctx rhs
  let (ctx, retOp) ←
    if bw = 32 then
      WfRewriter.createOp! ctx (.riscv op32) #[RegisterType.mk]
          #[lcastOp.getResult 0, rcastOp.getResult 0] #[] #[] props32 none
    else
      WfRewriter.createOp! ctx (.riscv op64) #[RegisterType.mk]
          #[lcastOp.getResult 0, rcastOp.getResult 0] #[] #[] props64 none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[lcastOp, rcastOp, retOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the width-agnostic binary RISC-V lowerings (`umax`/`umin`): match a two-operand
  LLVM integer op whose result has integer type `i64` or `i32`, cast both operands to registers,
  apply a single `riscv` op `rop` to the two registers, and cast the result back to the source
  type. Unlike `lowerBinaryWLocal`, `rop` is the *same* instruction at both bitwidths (the register
  already holds the correctly-represented value, so no `W` variant is needed), and the type guard
  reads the *result* type rather than the operands'.
-/
def lowerBinaryRegLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (rop : Riscv) (props : propertiesOf (.riscv rop))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := match? op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let (ctx, mOp) ← WfRewriter.createOp! ctx (.riscv rop) #[RegisterType.mk]
      #[lCastOp.getResult 0, rCastOp.getResult 0] #[] #[] props none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (mOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, mOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the width-agnostic *bitwise* binary RISC-V lowerings (`and`/`or`): match a
  two-operand LLVM integer op whose result has integer type `i64`, `i32`, `i8`, or `i1`, cast both
  operands to registers, apply a single bitwise `riscv` op `rop` to the two registers, and cast the
  result back to the source type.
-/
def lowerBitwiseRegLocal {P : Type}
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × P))
    (rop : Riscv) (props : propertiesOf (.riscv rop))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := match? op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 ∧ t.bitwidth ≠ 8 ∧ t.bitwidth ≠ 1 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let (ctx, mOp) ← WfRewriter.createOp! ctx (.riscv rop) #[RegisterType.mk]
      #[lCastOp.getResult 0, rCastOp.getResult 0] #[] #[] props none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (mOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, mOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the *signed* min/max RISC-V lowerings (`smax`/`smin`): match a two-operand LLVM
  integer op whose result has type `i64` or `i32`, cast both operands to registers, and apply a
  single signed `riscv` op `rop` (`max`/`min`).
-/
def lowerSignedMinMaxLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr))
    (rop : Riscv) (props : propertiesOf (.riscv rop))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := match? op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  /- For i32, sign-extend before the compare so negative values order correctly. -/
  if t.bitwidth = 32 then
    let (ctx, ls) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[lCastOp.getResult 0]
        #[] #[] () none
    let (ctx, rs) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[rCastOp.getResult 0]
        #[] #[] () none
    let (ctx, mOp) ← WfRewriter.createOp! ctx (.riscv rop) #[RegisterType.mk]
        #[ls.getResult 0, rs.getResult 0] #[] #[] props none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (mOp.getResult 0)
    some (ctx, some (#[lCastOp, rCastOp, ls, rs, mOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, mOp) ← WfRewriter.createOp! ctx (.riscv rop) #[RegisterType.mk]
        #[lCastOp.getResult 0, rCastOp.getResult 0] #[] #[] props none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (mOp.getResult 0)
    some (ctx, some (#[lCastOp, rCastOp, mOp, castBackOp], #[castBackOp.getResult 0]))

/--
  Shared shape of the *rotate* RISC-V lowerings (`fshl`/`fshr` whose two data operands are
  identical): match a funnel-shift LLVM op returning `(a, b, amt)`, require `a = b` (so the funnel
  shift is a rotate), require the result to have integer type `i64` or `i32`, cast the value operand
  `a` and the shift-amount operand `amt` to registers, apply `op64` (or its `W` variant `op32` for
  `i32`) to `(value, amount)`, and cast the result back to the source type.
-/
def lowerRotateLocal
    (match? : OperationPtr → IRContext OpCode → Option (ValuePtr × ValuePtr × ValuePtr))
    (op64 op32 : Riscv)
    (props64 : propertiesOf (.riscv op64)) (props32 : propertiesOf (.riscv op32))
    (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := match? op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  let (ctx, amtCastOp) ← castToRegLocal ctx amt
  let (ctx, rotOp) ←
    if t.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv op32) #[RegisterType.mk]
          #[valCastOp.getResult 0, amtCastOp.getResult 0] #[] #[] props32 none
    else
      WfRewriter.createOp! ctx (.riscv op64) #[RegisterType.mk]
          #[valCastOp.getResult 0, amtCastOp.getResult 0] #[] #[] props64 none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (rotOp.getResult 0)
  some (ctx, some (#[valCastOp, amtCastOp, rotOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `llvm.intr.ctlz` -> `riscv.clz`.
-/
def ctlz_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerUnaryWLocal matchCtlz .clz .clzw () () ctx op

/--
  `llvm.intr.ctlz` -> `riscv.clz`.
-/
def ctlz (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ctlz_local rewriter op opInBounds

/--
  `llvm.intr.cttz` -> `riscv.ctz`.
-/
def cttz_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerUnaryWLocal matchCttz .ctz .ctzw () () ctx op

/--
  `llvm.intr.cttz` -> `riscv.ctz`.
-/
def cttz (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite cttz_local rewriter op opInBounds

/--
  `llvm.intr.ctpop` -> `riscv.cpop`.
-/
def ctpop_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerUnaryWLocal matchCtpop .cpop .cpopw () () ctx op

/--
  `llvm.intr.ctpop` -> `riscv.cpop`.
-/
def ctpop (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ctpop_local rewriter op opInBounds

/--
  `llvm.intr.bswap` -> `riscv.rev8`.
-/
def bswap_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some operand := matchBswap op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  /- rev8 reverses all 8 bytes; for i32 the wanted bytes end up in the high 32 bits,
     so shift them down with srli 32. -/
  let (ctx, rev8Op) ← WfRewriter.createOp! ctx (.riscv .rev8) #[RegisterType.mk] #[castOp.getResult 0]
      #[] #[] () none
  if opType.bitwidth = 32 then
    let sh32 := RISCVImmediateProperties.mk (IntegerAttr.mk 32 (IntegerType.mk 64))
    let (ctx, srliOp) ← WfRewriter.createOp! ctx (.riscv .srli) #[RegisterType.mk] #[rev8Op.getResult 0]
        #[] #[] sh32 none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (srliOp.getResult 0)
    some (ctx, some (#[castOp, rev8Op, srliOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (rev8Op.getResult 0)
    some (ctx, some (#[castOp, rev8Op, castBackOp], #[castBackOp.getResult 0]))

/--
  `llvm.intr.bswap` -> `riscv.rev8`.
-/
def bswap (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bswap_local rewriter op opInBounds

/--
  One SWAR bit-reversal stage:
  `((x & mask) << shamt) | ((x >> shamt) & mask)`.
-/
def bitreverseStageLocal (mask shamt : Int) (ctx : WfIRContext OpCode) (input : ValuePtr) :
    Option (WfIRContext OpCode × Array OperationPtr × ValuePtr) := do
  let maskAttr := RISCVImmediateProperties.mk (IntegerAttr.mk mask (IntegerType.mk 64))
  let (ctx, maskOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] maskAttr none
  let (ctx, lowOp) ← WfRewriter.createOp! ctx (.riscv .and) #[RegisterType.mk]
      #[maskOp.getResult 0, input] #[] #[] () none
  let shamtAttr := RISCVImmediateProperties.mk (IntegerAttr.mk shamt (IntegerType.mk 64))
  let (ctx, lowShiftOp) ← WfRewriter.createOp! ctx (.riscv .slli) #[RegisterType.mk]
      #[lowOp.getResult 0] #[] #[] shamtAttr none
  let (ctx, highShiftOp) ← WfRewriter.createOp! ctx (.riscv .srli) #[RegisterType.mk]
      #[input] #[] #[] shamtAttr none
  let (ctx, highOp) ← WfRewriter.createOp! ctx (.riscv .and) #[RegisterType.mk]
      #[maskOp.getResult 0, highShiftOp.getResult 0] #[] #[] () none
  let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk]
      #[lowShiftOp.getResult 0, highOp.getResult 0] #[] #[] () none
  return (ctx, #[maskOp, lowOp, lowShiftOp, highShiftOp, highOp, orOp], orOp.getResult 0)

/--
  `llvm.intr.bitreverse` -> mask/shift/or stages followed by `riscv.rev8`.
-/
def bitreverse_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some operand := matchBitreverse op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  if opType.bitwidth = 32 then
    /- Use 32-bit masks so SWAR stages stay within the low 32 bits.
       rev8 brings bits to high 32; srli 32 moves them back down. -/
    let (ctx, ops1, x1) ← bitreverseStageLocal 0x55555555 1 ctx (castOp.getResult 0)
    let (ctx, ops2, x2) ← bitreverseStageLocal 0x33333333 2 ctx x1
    let (ctx, ops3, x3) ← bitreverseStageLocal 0x0f0f0f0f 4 ctx x2
    let (ctx, rev8Op) ← WfRewriter.createOp! ctx (.riscv .rev8) #[RegisterType.mk] #[x3]
        #[] #[] () none
    let sh32 := RISCVImmediateProperties.mk (IntegerAttr.mk 32 (IntegerType.mk 64))
    let (ctx, srliOp) ← WfRewriter.createOp! ctx (.riscv .srli) #[RegisterType.mk] #[rev8Op.getResult 0]
        #[] #[] sh32 none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (srliOp.getResult 0)
    some (ctx, some (#[castOp] ++ ops1 ++ ops2 ++ ops3 ++ #[rev8Op, srliOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, ops1, x1) ← bitreverseStageLocal 0x5555555555555555 1 ctx (castOp.getResult 0)
    let (ctx, ops2, x2) ← bitreverseStageLocal 0x3333333333333333 2 ctx x1
    let (ctx, ops3, x3) ← bitreverseStageLocal 0x0f0f0f0f0f0f0f0f 4 ctx x2
    let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .rev8) #[RegisterType.mk] #[x3]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
    some (ctx, some (#[castOp] ++ ops1 ++ ops2 ++ ops3 ++ #[retOp, castBackOp], #[castBackOp.getResult 0]))

/--
  `llvm.intr.bitreverse` -> mask/shift/or stages followed by `riscv.rev8`.
-/
def bitreverse (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bitreverse_local rewriter op opInBounds

/-- llvm.constant -> riscv.li -/
def constant_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some const := matchConstantIntOp op ctx
      | return (ctx, none)
  if const.type.bitwidth ≠ 64 ∧ const.type.bitwidth ≠ 32 ∧ const.type.bitwidth ≠ 8 ∧ const.type.bitwidth ≠ 1 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 ∧ type'.bitwidth ≠ 8 ∧ type'.bitwidth ≠ 1 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] {value := const} none
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type]
      #[newOp.getResult 0] #[] #[] () none
  some (ctx, some (#[newOp, castOp], #[castOp.getResult 0]))

/-- llvm.constant -> riscv.li -/
def constant (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite constant_local rewriter op opInBounds

/-- llvm.add -> riscv.add (riscv.addw for i32, keeps the result sign-extended) -/
def add_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchAdd .add .addw () () ctx op

/-- llvm.add -> riscv.add -/
def add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite add_local rewriter op opInBounds

/-- llvm.and -> riscv.and (bitwise, so one instruction for every legal width) -/
def and_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBitwiseRegLocal matchAnd .and () ctx op

/-- llvm.and -> riscv.and -/
def and (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite and_local rewriter op opInBounds

/-- llvm.ashr -> riscv.sra -/
def ashr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAshr op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 ∧ ltype.bitwidth ≠ 8 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 ∧ rtype.bitwidth ≠ 8 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 ∧ type'.bitwidth ≠ 8 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  if type'.bitwidth = 8 then
    let (ctx, lsOp) ← WfRewriter.createOp! ctx (.riscv .sextb) #[RegisterType.mk] #[lcastOp.getResult 0]
          #[] #[] () none
    let (ctx, sraOp) ← WfRewriter.createOp! ctx (.riscv .sra) #[RegisterType.mk] #[lsOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    let (ctx, castSraOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[sraOp.getResult 0]
      #[] #[] () none
    return (ctx, some (#[lcastOp, rcastOp, lsOp, sraOp, castSraOp], #[castSraOp.getResult 0]))
  /- sraw for i32 (sign-extends result), sra for i64 -/
  let (ctx, sraOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .sraw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .sra) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency -/
  let (ctx, castSraOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[sraOp.getResult 0]
      #[] #[] () none
  return (ctx, some (#[lcastOp, rcastOp, sraOp, castSraOp], #[castSraOp.getResult 0]))

/-- llvm.ashr -> riscv.sra -/
def ashr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ashr_local rewriter op opInBounds

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

  Every arm shares the same prologue (`icmpCastExtLocal`: cast both operands into registers, and
  sign-extend them when they are narrower than a register) and the same epilogue (cast the `i1`
  result back). Only the comparison sequence in between differs, and the five shapes it can take are
  the `icmpEmit*Local` combinators below, each of which is proven correct once in
  `RewriteProofs/LowerIcmp.lean`. -/

/-- The `i1` constant `1`, the immediate shared by the `sltiu`/`xori` arms. -/
def icmpOneImm : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))

/-- The immediate `0`, materialized by the `li` feeding the `sltu` of the `≠` arms. -/
def icmpZeroImm : RISCVImmediateProperties :=
  RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))

/-- A `riscv` sign-extension instruction usable as an `icmp` prologue: an opcode with no
    properties (`riscv.sextw`, `riscv.sextb`). Bundling the opcode with the proof keeps the
    prologue's `ext` argument non-dependent, so proofs can case on it directly. -/
structure IcmpExtOp where
  /-- The sign-extension opcode. -/
  op : Riscv
  /-- The opcode takes no properties. -/
  hprops : Riscv.propertiesOf op = Unit

/--
  Shared prologue of every `llvm.icmp` arm: cast both operands into registers and, when `ext` is
  `some e`, sign-extend each register with `e` (`riscv.sextw` for `i32`, `riscv.sextb` for `i8`).
  `castToRegLocal` zero-extends into the register, so without the fixup a negative narrow operand
  would look positive to the 64-bit signed comparison; sign-extension also preserves the unsigned
  order, so the unsigned comparisons stay correct too.

  Returns the created operations along with the two registers to compare.
-/
def icmpCastExtLocal (ctx : WfIRContext OpCode) (lhs rhs : ValuePtr) (ext : Option IcmpExtOp) :
    Option (WfIRContext OpCode × Array OperationPtr × ValuePtr × ValuePtr) := do
  let (ctx, lcastOp) ← castToRegLocal ctx lhs
  let (ctx, rcastOp) ← castToRegLocal ctx rhs
  match ext with
  | none => some (ctx, #[lcastOp, rcastOp], lcastOp.getResult 0, rcastOp.getResult 0)
  | some e =>
    let props : Riscv.propertiesOf e.op := cast e.hprops.symm ()
    let (ctx, lsOp) ← WfRewriter.createOp! ctx (.riscv e.op) #[RegisterType.mk]
      #[lcastOp.getResult 0] #[] #[] props none
    let (ctx, rsOp) ← WfRewriter.createOp! ctx (.riscv e.op) #[RegisterType.mk]
      #[rcastOp.getResult 0] #[] #[] props none
    some (ctx, #[lcastOp, rcastOp, lsOp, rsOp], lsOp.getResult 0, rsOp.getResult 0)

/-- `icmp` arm emitting a single register-register comparison `rop` (`slt`/`sltu`), whose operands
    are the two comparison registers, swapped when `swap` is set: `slt`/`sgt`/`ult`/`ugt`. -/
def icmpEmitCmpLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (lhs rhs : ValuePtr)
    (ext : Option IcmpExtOp)
    (rop : Riscv) (hrop : Riscv.propertiesOf rop = Unit) (swap : Bool) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let (ctx, pre, a, b) ← icmpCastExtLocal ctx lhs rhs ext
  let (u, v) := if swap then (b, a) else (a, b)
  let (ctx, cmpOp) ← WfRewriter.createOp! ctx (.riscv rop) #[RegisterType.mk] #[u, v]
    #[] #[] (cast hrop.symm ()) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (cmpOp.getResult 0)
  some (ctx, some (pre ++ #[cmpOp, castBackOp], #[castBackOp.getResult 0]))

/-- `icmp` arm emitting a register-register comparison `rop` followed by the immediate op `ropImm`
    applied to its result with the immediate `1`: `sle`/`sge`/`ule`/`uge` (`slt`/`sltu` then
    `xori _ 1`) and the generic `eq` (`xor` then `sltiu _ 1`). -/
def icmpEmitCmpImmLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (lhs rhs : ValuePtr)
    (ext : Option IcmpExtOp)
    (rop : Riscv) (hrop : Riscv.propertiesOf rop = Unit) (swap : Bool)
    (ropImm : Riscv) (hropImm : Riscv.propertiesOf ropImm = RISCVImmediateProperties) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let (ctx, pre, a, b) ← icmpCastExtLocal ctx lhs rhs ext
  let (u, v) := if swap then (b, a) else (a, b)
  let (ctx, cmpOp) ← WfRewriter.createOp! ctx (.riscv rop) #[RegisterType.mk] #[u, v]
    #[] #[] (cast hrop.symm ()) none
  let (ctx, immOp) ← WfRewriter.createOp! ctx (.riscv ropImm) #[RegisterType.mk]
    #[cmpOp.getResult 0] #[] #[] (cast hropImm.symm icmpOneImm) none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (immOp.getResult 0)
  some (ctx, some (pre ++ #[cmpOp, immOp, castBackOp], #[castBackOp.getResult 0]))

/-- `icmp` arm emitting `sltiu a 1` (`seqz`) on the left comparison register: the `eq`-against-zero
    peephole. -/
def icmpEmitSeqzLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (lhs rhs : ValuePtr)
    (ext : Option IcmpExtOp) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let (ctx, pre, a, _) ← icmpCastExtLocal ctx lhs rhs ext
  let (ctx, immOp) ← WfRewriter.createOp! ctx (.riscv .sltiu) #[RegisterType.mk] #[a]
    #[] #[] icmpOneImm none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (immOp.getResult 0)
  some (ctx, some (pre ++ #[immOp, castBackOp], #[castBackOp.getResult 0]))

/-- `icmp` arm emitting `sltu 0 a` (`snez`) on the left comparison register: the `ne`-against-zero
    peephole. The `riscv.li 0` becomes `x0` under `riscv-combine` (see `li_zero_to_x0`). -/
def icmpEmitSnezLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (lhs rhs : ValuePtr)
    (ext : Option IcmpExtOp) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let (ctx, pre, a, _) ← icmpCastExtLocal ctx lhs rhs ext
  let (ctx, liOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
    #[] #[] icmpZeroImm none
  let (ctx, cmpOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk]
    #[liOp.getResult 0, a] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (cmpOp.getResult 0)
  some (ctx, some (pre ++ #[liOp, cmpOp, castBackOp], #[castBackOp.getResult 0]))

/-- `icmp` arm emitting `sltu 0 (xor b a)` (`snez` of the difference): the generic `ne`. -/
def icmpEmitXorSnezLocal (ctx : WfIRContext OpCode) (op : OperationPtr) (lhs rhs : ValuePtr)
    (ext : Option IcmpExtOp) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let (ctx, pre, a, b) ← icmpCastExtLocal ctx lhs rhs ext
  let (ctx, xorOp) ← WfRewriter.createOp! ctx (.riscv .xor) #[RegisterType.mk] #[b, a]
    #[] #[] () none
  let (ctx, liOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
    #[] #[] icmpZeroImm none
  let (ctx, cmpOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk]
    #[liOp.getResult 0, xorOp.getResult 0] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (cmpOp.getResult 0)
  some (ctx, some (pre ++ #[xorOp, liOp, cmpOp, castBackOp], #[castBackOp.getResult 0]))

/-- The sign-extension instruction needed to compare two `bw`-wide operands in a register, if any. -/
def icmpExtOf (bw : Nat) : Option IcmpExtOp :=
  if bw = 32 then some ⟨.sextw, rfl⟩ else if bw = 8 then some ⟨.sextb, rfl⟩ else none

/-- llvm.icmp -> riscv comparison sequence (see the arms above). -/
def icmp_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, property) := matchIcmp op ctx | return (ctx, none)
  /- support `i64`, `i32` and `i8` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 ∧ ltype.bitwidth ≠ 8 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 ∧ rtype.bitwidth ≠ 8 then return (ctx, none)
  /- The result is cast back for type consistency, so it must be an integer type. -/
  let .integerType _ := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  let ext := icmpExtOf ltype.bitwidth
  /- Peephole for `eq`/`ne`: when the rhs is a constant `0`, the `xor` is unnecessary and the
     comparison is against the left register directly (`seqz`/`snez`). Canonicalization runs before
     isel and moves the constant to the rhs, so we only check that side.
     LLVM: `Pat<(riscv_seteq GPR:$rs1), (SLTIU GPR:$rs1, 1)>` and
     `Pat<(riscv_setne GPR:$rs1), (SLTU (XLenVT X0), GPR:$rs1)>`.
     https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1649 -/
  let rhsIsZero := (matchConstantZero rhs ctx).isSome
  match property.predicate with
  | .eq =>
    if rhsIsZero then icmpEmitSeqzLocal ctx op lhs rhs ext
    else icmpEmitCmpImmLocal ctx op lhs rhs ext .xor rfl true .sltiu rfl
  | .ne =>
    if rhsIsZero then icmpEmitSnezLocal ctx op lhs rhs ext
    else icmpEmitXorSnezLocal ctx op lhs rhs ext
  | .slt => icmpEmitCmpLocal ctx op lhs rhs ext .slt rfl false
  | .sgt => icmpEmitCmpLocal ctx op lhs rhs ext .slt rfl true
  | .ult => icmpEmitCmpLocal ctx op lhs rhs ext .sltu rfl false
  | .ugt => icmpEmitCmpLocal ctx op lhs rhs ext .sltu rfl true
  | .sge => icmpEmitCmpImmLocal ctx op lhs rhs ext .slt rfl false .xori rfl
  | .sle => icmpEmitCmpImmLocal ctx op lhs rhs ext .slt rfl true .xori rfl
  | .uge => icmpEmitCmpImmLocal ctx op lhs rhs ext .sltu rfl false .xori rfl
  | .ule => icmpEmitCmpImmLocal ctx op lhs rhs ext .sltu rfl true .xori rfl

/-- llvm.icmp -> riscv comparison sequence (see `icmp_local`). -/
def icmp (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite icmp_local rewriter op opInBounds

/-- llvm.or -> riscv.or (bitwise, so one instruction for every legal width) -/
def or_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBitwiseRegLocal matchOr .or () ctx op

/-- llvm.or -> riscv.or -/
def or (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite or_local rewriter op opInBounds

/-- llvm.xor -> riscv.xor (no `W` variant needed: xor is bitwise) -/
def xor_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchXor .xor .xor () () ctx op

/-- llvm.xor -> riscv.xor -/
def xor (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xor_local rewriter op opInBounds

/-- llvm.mul -> riscv.mul (riscv.mulw for i32, sign-extends the result) -/
def mul_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchMul .mul .mulw () () ctx op

/-- llvm.mul -> riscv.mul -/
def mul (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mul_local rewriter op opInBounds

/-- llvm.sdiv -> riscv.div (riscv.divw for i32) -/
def sdiv_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchSdiv .div .divw () () ctx op

/-- llvm.sdiv -> riscv.div -/
def sdiv (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sdiv_local rewriter op opInBounds

/-- llvm.udiv -> riscv.divu (riscv.divuw for i32) -/
def udiv_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchUdiv .divu .divuw () () ctx op

/-- llvm.udiv -> riscv.divu -/
def udiv (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite udiv_local rewriter op opInBounds

/-- llvm.srem -> riscv.rem (riscv.remw for i32) -/
def srem_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchSrem .rem .remw () () ctx op

/-- llvm.srem -> riscv.rem -/
def srem (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite srem_local rewriter op opInBounds

/-- llvm.urem -> riscv.remu (riscv.remuw for i32) -/
def urem_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchUrem .remu .remuw () () ctx op

/-- llvm.urem -> riscv.remu -/
def urem (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite urem_local rewriter op opInBounds

/-- llvm.sub -> riscv.sub (riscv.subw for i32) -/
def sub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryWLocal matchSub .sub .subw () () ctx op

/-- llvm.sub -> riscv.sub -/
def sub (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sub_local rewriter op opInBounds

/--
  llvm.sext %x `i8`  to `i32` -> riscv.sextb %x
  llvm.sext %x `i8`  to `i64` -> riscv.sextb %x
  llvm.sext %x `i16` to `i64` -> riscv.sexth %x
  llvm.sext %x `i16` to `i32` -> riscv.sexth %x
  llvm.sext %x `i32` to `i64` -> riscv.sextw %x
-/
def sext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerExtLocal matchSext .sextb .sexth .sextw () () () ctx op

/--
  llvm.sext -> riscv.sextb/sexth/sextw (see `sext_local`).
-/
def sext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sext_local rewriter op opInBounds

/--
  llvm.zext %x `i8`  to `i32` -> riscv.zextb %x
  llvm.zext %x `i8`  to `i64` -> riscv.zextb %x
  llvm.zext %x `i16` to `i64` -> riscv.zexth %x
  llvm.zext %x `i16` to `i32` -> riscv.zexth %x
  llvm.zext %x `i32` to `i64` -> riscv.zextw %x
-/
def zext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerExtLocal matchZext .zextb .zexth .zextw () () () ctx op

/--
  llvm.zext -> riscv.zexth/zextw (see `zext_local`).
-/
def zext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite zext_local rewriter op opInBounds

/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!riscv.reg) : iY
  where `iY`'s width is smaller than `iX`'s.
  Also accepts the byte type.
-/
def trunc_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchTrunc op ctx | return (ctx, none)
  let opType := (operand.getType! ctx.raw)
  let resType := ((op.getResult 0).get! ctx.raw).type
  let shouldTruncate := match opType.val, resType.val with
    | .integerType _, .integerType _ => true
    | .byteType _, .byteType _ => true
    | _, _ => false
  if !shouldTruncate
  then return (ctx, none)
  let some opBw := getIntByteTypeBitwidth opType | return (ctx, none)
  let some resBw := getIntByteTypeBitwidth resType | return (ctx, none)
  if opBw ≤ resBw then return (ctx, none)
  /- Restrict to the register-representable widths: the operand is held in a 64-bit register, so an
     operand wider than 64 bits (or a result wider than 64 bits) would lose bits in the round trip.
     Limiting to `{8, 16, 32, 64}` keeps the lowering sound and makes the widths concrete. -/
  if opBw ∉ [8, 16, 32, 64] ∨ resBw ∉ [8, 16, 32, 64] then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  /- Then, cast register to expected output width. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[resType] #[opCastOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, castOp], #[castOp.getResult 0]))

/--
  llvm.trunc -> builtin_unrealized_conversion_cast (see `trunc_local`).
-/
def trunc (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite trunc_local rewriter op opInBounds

/-- llvm.shl -> riscv.sll -/
def shl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerByteBinaryWLocal matchShl .sll .sllw () () ctx op

/-- llvm.shl -> riscv.sll -/
def shl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite shl_local rewriter op opInBounds

/-- llvm.lshr -> riscv.srl (riscv.srlw for i32) -/
def lshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerByteBinaryWLocal matchLshr .srl .srlw () () ctx op

/-- llvm.shl -> riscv.srl -/
def lshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite lshr_local rewriter op opInBounds

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

/--
  llvm.bitcast t1 %x to t2 -> builtin_unrealized_conversion_cast
  Integers, bytes, and pointers are all lowered to !riscv.reg, making this basically a no-op.
  The `byte -> ptr` case is excluded.
-/
def bitcast_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchBitcast op ctx | return (ctx, none)
  let opType := operand.getType! ctx.raw
  let resType := ((op.getResult 0).get! ctx.raw).type
  if ¬ checkBitcastType opType ∨ ¬ checkBitcastType resType then return (ctx, none)
  if isBitcastByteToPtr opType resType then return (ctx, none)
  let some opBw := Attribute.bitwidthOfType opType | return (ctx, none)
  let some resBw := Attribute.bitwidthOfType resType | return (ctx, none)
  if opBw ∉ [8, 16, 32, 64] ∨ resBw ∉ [8, 16, 32, 64] then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  /- Then, cast register to expected output type. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[resType] #[opCastOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, castOp], #[castOp.getResult 0]))

def bitcast (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite bitcast_local rewriter op opInBounds

/-- llvm.load -> riscv.ld (i64) / riscv.lw (i32) / riscv.lb (i8) -/
def load_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (ptr, _) := matchLoad op ctx | return (ctx, none)
  /- support `i64`, `i32` and `i8` (the loaded value type) -/
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 ∧ type'.bitwidth ≠ 8 then return (ctx, none)
  /- cast ptr (!llvm.ptr) -> register -/
  let (ctx, pcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[ptr]
      #[] #[] () none
  /- 64-bit `riscv.ld`, or its `lw` (i32) / `lb` (i8) variants -/
  let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (ctx, ldOp) ←
    if type'.bitwidth = 8 then
      WfRewriter.createOp! ctx (.riscv .lb) #[RegisterType.mk] #[pcastOp.getResult 0]
        #[] #[] zero none
    else if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .lw) #[RegisterType.mk] #[pcastOp.getResult 0]
        #[] #[] zero none
    else
      WfRewriter.createOp! ctx (.riscv .ld) #[RegisterType.mk] #[pcastOp.getResult 0]
        #[] #[] zero none
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[ldOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[pcastOp, ldOp, castOp], #[castOp.getResult 0]))

/-- llvm.load -> riscv.ld (i64) / riscv.lw (i32) / riscv.lb (i8) -/
def load (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite load_local rewriter op opInBounds

/-- llvm.store -> riscv.sd (i64) / riscv.sw (i32) / riscv.sb (i8) -/
def store_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (arg, ptr, _) := matchStore op ctx | return (ctx, none)
  /- support `i64`, `i32` and `i8` (the stored value type) -/
  let type := arg.getType! ctx.raw
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 ∧ type'.bitwidth ≠ 8 then return (ctx, none)
  /- cast ptr (!llvm.ptr) -> register -/
  let (ctx, pcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[ptr]
      #[] #[] () none
  /- cast value (i64/i32/i8) -> register -/
  let (ctx, valcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[arg]
      #[] #[] () none
  /- 64-bit `riscv.sd`, or its `sw` (i32, low 4 bytes) / `sb` (i8, low byte), with offset zero: operands are (addr, val), no results -/
  let zero := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (ctx, sdOp) ←
    if type'.bitwidth = 8 then
      WfRewriter.createOp! ctx (.riscv .sb) #[] #[valcastOp.getResult 0, pcastOp.getResult 0]
        #[] #[] zero none
    else if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .sw) #[] #[valcastOp.getResult 0, pcastOp.getResult 0]
        #[] #[] zero none
    else
      WfRewriter.createOp! ctx (.riscv .sd) #[] #[valcastOp.getResult 0, pcastOp.getResult 0]
        #[] #[] zero none
  some (ctx, some (#[pcastOp, valcastOp, sdOp], #[]))

/-- llvm.store -> riscv.sd (i64) / riscv.sw (i32) / riscv.sb (i8) -/
def store (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite store_local rewriter op opInBounds

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the byte size of the element type.
-/
def getelementptr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (ptr, idx, properties) := matchGetelementptr op ctx | return (ctx, none)
  /- Bail unless it's a single dynamic index with no trailing constant indices. -/
  if properties.rawConstantIndices.values ≠ #[(-2147483648 : Int)] then return (ctx, none)
  /- The index must be `i64`. -/
  let .integerType itype := (idx.getType! ctx.raw).val | return (ctx, none)
  if itype.bitwidth ≠ 64 then return (ctx, none)
  let some scale := Attribute.sizeOfType properties.elem_type.val | return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let (ctx, pcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[ptr]
      #[] #[] () none
  let (ctx, icastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[idx]
      #[] #[] () none
  let pReg := pcastOp.getResult 0
  let iReg := icastOp.getResult 0
  let (ctx, gepOps, retOp) ← match scale with
    | 1 =>
      /- ptr + idx -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx (.riscv .add) #[RegisterType.mk] #[pReg, iReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | 2 =>
      /- (idx << 1) + ptr -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx (.riscv .sh1add) #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | 4 =>
      /- (idx << 2) + ptr -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx (.riscv .sh2add) #[RegisterType.mk] #[iReg, pReg]
        #[] #[] () none
      pure (ctx, #[addOp], addOp)
    | 8 =>
      /- (idx << 3) + ptr -/
      let (ctx, addOp) ← WfRewriter.createOp! ctx (.riscv .sh3add) #[RegisterType.mk] #[iReg, pReg]
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
        let k := RISCVImmediateProperties.mk (IntegerAttr.mk (Nat.log2 scale) (IntegerType.mk 64))
        let (ctx, slliOp) ← WfRewriter.createOp! ctx (.riscv .slli) #[RegisterType.mk] #[iReg]
          #[] #[] k none
        let (ctx, addOp) ← WfRewriter.createOp! ctx (.riscv .add) #[RegisterType.mk] #[pReg, slliOp.getResult 0]
          #[] #[] () none
        pure (ctx, #[slliOp, addOp], addOp)
      else
        /- arbitrary scale: ptr + idx * scale -/
        let s := RISCVImmediateProperties.mk (IntegerAttr.mk scale (IntegerType.mk 64))
        let (ctx, liOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
          #[] #[] s none
        let (ctx, mulOp) ← WfRewriter.createOp! ctx (.riscv .mul) #[RegisterType.mk] #[iReg, liOp.getResult 0]
          #[] #[] () none
        let (ctx, addOp) ← WfRewriter.createOp! ctx (.riscv .add) #[RegisterType.mk] #[pReg, mulOp.getResult 0]
          #[] #[] () none
        pure (ctx, #[liOp, mulOp, addOp], addOp)
  /- Cast the resulting register back to `!llvm.ptr`. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[pcastOp, icastOp] ++ gepOps ++ #[castOp], #[castOp.getResult 0]))

/--
  Lower a single-dynamic-index `llvm.getelementptr` computing `ptr + idx * scale`,
  where `scale` is the byte size of the element type.
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
  let some (cond, tval, fval) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some _ := matchConstantZero fval ctx | return (ctx, none)
  let (ctx, tCastOp) ← castToRegLocal ctx tval
  let (ctx, condCastOp) ← castToRegLocal ctx cond
  let (ctx, czOp) ← WfRewriter.createOp! ctx (.riscv .czeroeqz) #[RegisterType.mk] #[tCastOp.getResult 0, condCastOp.getResult 0]
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
  let some (cond, tval, fval) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let some _ := matchConstantZero tval ctx | return (ctx, none)
  let (ctx, fCastOp) ← castToRegLocal ctx fval
  let (ctx, condCastOp) ← castToRegLocal ctx cond
  let (ctx, czOp) ← WfRewriter.createOp! ctx (.riscv .czeronez) #[RegisterType.mk] #[fCastOp.getResult 0, condCastOp.getResult 0]
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
  let some (cond, tval, fval) := matchSelect op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 ∧ t.bitwidth ≠ 1 then return (ctx, none)
  let (ctx, tCastOp) ← castToRegLocal ctx tval
  let (ctx, fCastOp) ← castToRegLocal ctx fval
  let (ctx, condCastOp) ← castToRegLocal ctx cond
  let (ctx, eqzOp) ← WfRewriter.createOp! ctx (.riscv .czeroeqz) #[RegisterType.mk] #[tCastOp.getResult 0, condCastOp.getResult 0]
      #[] #[] () none
  let (ctx, nezOp) ← WfRewriter.createOp! ctx (.riscv .czeronez) #[RegisterType.mk] #[fCastOp.getResult 0, condCastOp.getResult 0]
      #[] #[] () none
  let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk]
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
def smax_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerSignedMinMaxLocal matchSmax .max () ctx op

/-- llvm.intr.smax -> riscv.max -/
def smax (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite smax_local rewriter op opInBounds

/-- llvm.intr.smin -> riscv.min -/
def smin_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerSignedMinMaxLocal matchSmin .min () ctx op

/-- llvm.intr.smin -> riscv.min -/
def smin (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite smin_local rewriter op opInBounds

/-- llvm.intr.umax -> riscv.maxu -/
def umax_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryRegLocal matchUmax .maxu () ctx op

/-- llvm.intr.umax -> riscv.maxu -/
def umax (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite umax_local rewriter op opInBounds

/-- llvm.intr.umin -> riscv.minu -/
def umin_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerBinaryRegLocal matchUmin .minu () ctx op

/-- llvm.intr.umin -> riscv.minu -/
def umin (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite umin_local rewriter op opInBounds

/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol (riscv.rolw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerRotateLocal matchFshl .rol .rolw () () ctx op

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
  RISCVImmediateProperties.mk (IntegerAttr.mk value (IntegerType.mk 64))

def createRISCVImmLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = RISCVImmediateProperties)
    (operands : Array ValuePtr) (value : Int) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] operands #[] #[]
      (cast h.symm (mkRISCVImm value)) none

def createRISCVUnitLocal (ctx : WfIRContext OpCode)
    (dst : Riscv) (h : Riscv.propertiesOf dst = Unit) (operands : Array ValuePtr) :
    Option (WfIRContext OpCode × OperationPtr) :=
  WfRewriter.createOp! ctx (.riscv dst) #[RegisterType.mk] operands #[] #[]
      (cast h.symm ()) none

def signedSatSelectLocal (ctx : WfIRContext OpCode) (op : OperationPtr)
    (wrapped overflow sat : ValuePtr) :
    Option (WfIRContext OpCode × Array OperationPtr × Array ValuePtr) := do
  let (ctx, wrappedOrZero) ← WfRewriter.createOp! ctx (.riscv .czeronez) #[RegisterType.mk]
      #[wrapped, overflow] #[] #[] () none
  let (ctx, satOrZero) ← WfRewriter.createOp! ctx (.riscv .czeroeqz) #[RegisterType.mk]
      #[sat, overflow] #[] #[] () none
  let (ctx, selectOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk]
      #[satOrZero.getResult 0, wrappedOrZero.getResult 0] #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (selectOp.getResult 0)
  return (ctx, #[wrappedOrZero, satOrZero, selectOp, castBackOp], #[castBackOp.getResult 0])

/-- llvm.intr.sadd.sat.i64 -> LLVM's RV64+Zicond signed saturating-add sequence.
    Wrapped `add` + SADDO overflow `(rhs >>u 63) ^ (sum <s lhs)`
    (TargetLowering.cpp:12432 `expandAddSubSat`, overflow at 13072
    `expandSADDSUBO` add branch; sat endpoint `(sum >>s 63) ^ INT_MIN` at 12554). -/
def saddSat_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchSaddSat op ctx | return (ctx, none)
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
  let some (lhs, rhs) := matchSsubSat op ctx | return (ctx, none)
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
  let some (lhs, rhs) := matchUaddSat op ctx | return (ctx, none)
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
  let some (lhs, rhs) := matchUsubSat op ctx | return (ctx, none)
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
  let some (lhs, rhs) := matchSshlSat op ctx | return (ctx, none)
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
  let some (lhs, rhs) := matchUshlSat op ctx | return (ctx, none)
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
  let some val := matchAbs op ctx | return (ctx, none)
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

/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol.
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite fshl_local rewriter op opInBounds

/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror (riscv.rorw for i32).
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) :=
  lowerRotateLocal matchFshr .ror .rorw () () ctx op

/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror.
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite fshr_local rewriter op opInBounds

/-- llvm.intr.fshr with identical data operands and a constant shift amount is a
    constant rotate-right: -> riscv.rori (mirrors `PatGprImm<rotr, RORI>`). -/
def fshrConst_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshr op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let some amtAttr := matchConstantIntVal amt ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  if t.bitwidth = 32 then
    let sh : Int := ((amtAttr.value % 32) + 32) % 32
    let imm := RISCVImmediateProperties.mk (IntegerAttr.mk sh (IntegerType.mk 64))
    let (ctx, roriOp) ← WfRewriter.createOp! ctx (.riscv .roriw) #[RegisterType.mk] #[valCastOp.getResult 0]
        #[] #[] imm none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
    some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))
  else
    /- The funnel-shift amount is taken modulo the bit width. -/
    let sh : Int := ((amtAttr.value % 64) + 64) % 64
    let imm := RISCVImmediateProperties.mk (IntegerAttr.mk sh (IntegerType.mk 64))
    let (ctx, roriOp) ← WfRewriter.createOp! ctx (.riscv .rori) #[RegisterType.mk] #[valCastOp.getResult 0]
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
  let some (a, b, amt) := matchFshl op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let some amtAttr := matchConstantIntVal amt ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  if t.bitwidth = 32 then
    /- rotate-left by `sh` == rotate-right by `32 - sh` (mod 32). -/
    let sh : Int := ((amtAttr.value % 32) + 32) % 32
    let imm : Int := (32 - sh) % 32
    let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm (IntegerType.mk 64))
    let (ctx, roriOp) ← WfRewriter.createOp! ctx (.riscv .roriw) #[RegisterType.mk] #[valCastOp.getResult 0]
        #[] #[] immProps none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (roriOp.getResult 0)
    some (ctx, some (#[valCastOp, roriOp, castBackOp], #[castBackOp.getResult 0]))
  else
    /- rotate-left by `sh` == rotate-right by `64 - sh` (mod 64). -/
    let sh : Int := ((amtAttr.value % 64) + 64) % 64
    let imm : Int := (64 - sh) % 64
    let immProps := RISCVImmediateProperties.mk (IntegerAttr.mk imm (IntegerType.mk 64))
    let (ctx, roriOp) ← WfRewriter.createOp! ctx (.riscv .rori) #[RegisterType.mk] #[valCastOp.getResult 0]
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
  let some (a, b, amt) := matchFshl op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx a
  let (ctx, yCastOp) ← castToRegLocal ctx b
  let (ctx, zCastOp) ← castToRegLocal ctx amt
  /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
  let notImm := RISCVImmediateProperties.mk (IntegerAttr.mk (-1) (IntegerType.mk 64))
  let (ctx, notzOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[zCastOp.getResult 0]
      #[] #[] notImm none
  let oneImm := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
  /- shx = x << z ; shy = (y >> 1) >> ~z ; result = shx | shy. The i32 form uses
     the `w` shifts (only the low 32 bits of the `or` are observed). -/
  if t.bitwidth = 32 then
    let (ctx, shxOp) ← WfRewriter.createOp! ctx (.riscv .sllw) #[RegisterType.mk] #[xCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, y1Op) ← WfRewriter.createOp! ctx (.riscv .srliw) #[RegisterType.mk] #[yCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx (.riscv .srlw) #[RegisterType.mk] #[y1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
    some (ctx, some (#[xCastOp, yCastOp, zCastOp, notzOp, shxOp, y1Op, shyOp, orOp, castBackOp],
      #[castBackOp.getResult 0]))
  else
    let (ctx, shxOp) ← WfRewriter.createOp! ctx (.riscv .sll) #[RegisterType.mk] #[xCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, y1Op) ← WfRewriter.createOp! ctx (.riscv .srli) #[RegisterType.mk] #[yCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx (.riscv .srl) #[RegisterType.mk] #[y1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
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
  let some (a, b, amt) := matchFshr op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, xCastOp) ← castToRegLocal ctx a
  let (ctx, yCastOp) ← castToRegLocal ctx b
  let (ctx, zCastOp) ← castToRegLocal ctx amt
  /- ~z, the inverse shift amount; the shift instruction masks it modulo `w`. -/
  let notImm := RISCVImmediateProperties.mk (IntegerAttr.mk (-1) (IntegerType.mk 64))
  let (ctx, notzOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[zCastOp.getResult 0]
      #[] #[] notImm none
  let oneImm := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
  /- shx = (x << 1) << ~z ; shy = y >> z ; result = shx | shy. The i32 form uses
     the `w` shifts (only the low 32 bits of the `or` are observed). -/
  if t.bitwidth = 32 then
    let (ctx, x1Op) ← WfRewriter.createOp! ctx (.riscv .slliw) #[RegisterType.mk] #[xCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shxOp) ← WfRewriter.createOp! ctx (.riscv .sllw) #[RegisterType.mk] #[x1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx (.riscv .srlw) #[RegisterType.mk] #[yCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (orOp.getResult 0)
    some (ctx, some (#[xCastOp, yCastOp, zCastOp, notzOp, x1Op, shxOp, shyOp, orOp, castBackOp],
      #[castBackOp.getResult 0]))
  else
    let (ctx, x1Op) ← WfRewriter.createOp! ctx (.riscv .slli) #[RegisterType.mk] #[xCastOp.getResult 0]
        #[] #[] oneImm none
    let (ctx, shxOp) ← WfRewriter.createOp! ctx (.riscv .sll) #[RegisterType.mk] #[x1Op.getResult 0, notzOp.getResult 0]
        #[] #[] () none
    let (ctx, shyOp) ← WfRewriter.createOp! ctx (.riscv .srl) #[RegisterType.mk] #[yCastOp.getResult 0, zCastOp.getResult 0]
        #[] #[] () none
    let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk] #[shxOp.getResult 0, shyOp.getResult 0]
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
  let some _ := matchPoison op ctx | return (ctx, none)
  let imm := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
  let (ctx, liOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
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
  let some operand := matchFreeze op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType retType := type.val | return (ctx, none)
  if (opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32) ∨ (retType.bitwidth ≠ 64 ∧ retType.bitwidth ≠ 32) then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  /- Then, cast register to expected output width. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[opCastOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, castOp], #[castOp.getResult 0]))

/-- llvm.freeze arg : Int w ->
  unrealized_conversion_cast (unrealized_conversion_cast arg : Int w -> Reg) : Reg -> Int w -/
def freeze (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite freeze_local rewriter op opInBounds

/-! # Pass implementation -/

def ISelPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  /- Early loop: multi-instruction fusion patterns that must run before the
     per-op lowerings consume their operands. -/
  /- Main loop: the existing per-op lowerings. -/
  let pattern := RewritePattern.GreedyRewritePattern #[selectCzeroeqz, selectCzeronez, selectGeneral, ctlz, cttz, ctpop, bswap, bitreverse, constant, add, and, ashr, icmp, or, xor, mul,
    sdiv, udiv, srem, urem, sext, zext, trunc, shl, lshr, sub, bitcast, load, getelementptr, store,
    smax, smin, umax, umin, saddSat, ssubSat, uaddSat, usubSat, sshlSat, ushlSat, abs,
    fshlConst, fshrConst, fshl, fshr, fshlGeneral, fshrGeneral, poisonConst, freeze]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
