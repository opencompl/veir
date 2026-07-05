import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
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
  `llvm.intr.ctlz` -> `riscv.clz`.
-/
def ctlz_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchCtlz op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  let (ctx, retOp) ←
    if opType.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .clzw) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .clz) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[castOp, retOp, castBackOp], #[castBackOp.getResult 0]))

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
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchCttz op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  let (ctx, retOp) ←
    if opType.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .ctzw) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .ctz) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[castOp, retOp, castBackOp], #[castBackOp.getResult 0]))

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
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some operand := matchCtpop op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if opType.bitwidth ≠ 64 ∧ opType.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, castOp) ← castToRegLocal ctx operand
  let (ctx, retOp) ←
    if opType.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .cpopw) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .cpop) #[RegisterType.mk] #[castOp.getResult 0]
          #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (retOp.getResult 0)
  some (ctx, some (#[castOp, retOp, castBackOp], #[castBackOp.getResult 0]))

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
  if const.type.bitwidth ≠ 64 ∧ const.type.bitwidth ≠ 32 ∧ const.type.bitwidth ≠ 8 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 ∧ type'.bitwidth ≠ 8 then return (ctx, none)
  let (ctx, newOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
      #[] #[] {value := const} none
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type]
      #[newOp.getResult 0] #[] #[] () none
  some (ctx, some (#[newOp, castOp], #[castOp.getResult 0]))

/-- llvm.constant -> riscv.li -/
def constant (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite constant_local rewriter op opInBounds

/-- llvm.add -> riscv.add -/
def add_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAdd op ctx | return (ctx, none)
  /- support `i64` and `i32` (experiment) -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- 64-bit add, or its 32-bit `W` variant for i32 (keeps the result sign-extended) -/
  let (ctx, addOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .addw) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .add) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
        #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castAddOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[addOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, addOp, castAddOp], #[castAddOp.getResult 0]))

/-- llvm.add -> riscv.add -/
def add (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite add_local rewriter op opInBounds

/-- llvm.and -> riscv.and -/
def and_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchAnd op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- Actual `riscv.and` -/
  let (ctx, andOp) ← WfRewriter.createOp! ctx (.riscv .and) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castAddOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[andOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, andOp, castAddOp], #[castAddOp.getResult 0]))

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
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- sraw for i32 (sign-extends result), sra for i64 -/
  let (ctx, sraOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .sraw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .sra) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castSraOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[sraOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, sraOp, castSraOp], #[castSraOp.getResult 0]))

/-- llvm.ashr -> riscv.sra -/
def ashr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite ashr_local rewriter op opInBounds

/--
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
-/
def icmp_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, property) := matchIcmp op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  /- Casting is necessary regardless of the predicate. -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- For i32, sign-extend operands so both signed and unsigned comparisons work correctly.
     Zero-extended i32 negatives look positive in 64-bit signed arithmetic without this. -/
  let (ctx, extOps, lCmpReg, rCmpReg) ←
    if ltype.bitwidth = 32 then do
      let (ctx, ls) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[lcastOp.getResult 0]
          #[] #[] () none
      let (ctx, rs) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[rcastOp.getResult 0]
          #[] #[] () none
      pure (ctx, #[ls, rs], ls.getResult 0, rs.getResult 0)
    else
      pure (ctx, #[], lcastOp.getResult 0, rcastOp.getResult 0)
  /- Casting back result for type consistency is always necessary. -/
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType _ := type.val | return (ctx, none)
  /- Match depending on the predicate and build correct lowering. -/
  let (ctx, predOps, retOp) ← match property.predicate with
    | .eq =>
      /- Peephole: when the rhs is a constant 0, `a == 0` lowers directly to
         `riscv.sltiu a 1` (seqz) with no xor. Otherwise fall back to the generic
         `riscv.sltiu (riscv.xor lhs rhs) 1` idiom. Canonicalization runs before
         isel and moves the constant to the rhs, so we only check that side.
         LLVM: `Pat<(riscv_seteq GPR:$rs1), (SLTIU GPR:$rs1, 1)>` (`selectSETEQ`
         normalizes `a == 0` to the zero-compare form first).
         https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1649 -/
      let zeroCmpReg :=
        if (matchConstantZero rhs ctx).isSome then some lCmpReg
        else none
      match zeroCmpReg with
      | some cmpReg =>
        /- llvm.icmp eq a 0  -> riscv.sltiu a 1 (seqz) -/
        let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
        let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sltiu) #[RegisterType.mk] #[cmpReg]
          #[] #[] c1 none
        pure (ctx, #[retOp], retOp)
      | none =>
        /- llvm.icmp eq lhs rhs  -> riscv.sltiu (riscv.xor lhs rhs) 1 -/
        let (ctx, xorOp) ← WfRewriter.createOp! ctx (.riscv .xor) #[RegisterType.mk] #[rCmpReg, lCmpReg]
          #[] #[] () none
        let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
        let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sltiu) #[RegisterType.mk] #[xorOp.getResult 0]
          #[] #[] c1 none
        pure (ctx, #[xorOp, retOp], retOp)
    | .ne =>
      /- Peephole: when the rhs is a constant 0, `a != 0` lowers directly to
         `riscv.sltu 0 a` (snez) with no xor. Otherwise fall back to the generic
         `riscv.sltu 0 (riscv.xor lhs rhs)` idiom. Canonicalization runs before
         isel and moves the constant to the rhs, so we only check that side.
         The `riscv.li 0` feeding `sltu` becomes `x0` under `riscv-combine` (see
         `li_zero_to_x0`), matching LLVM's `SLTU X0, rs1`.
         LLVM: `Pat<(riscv_setne GPR:$rs1), (SLTU (XLenVT X0), GPR:$rs1)>`.
         https://github.com/llvm/llvm-project/blob/d9906882fc613471ab51e7185094efae893066de/llvm/lib/Target/RISCV/RISCVInstrInfo.td#L1650 -/
      let zeroCmpReg :=
        if (matchConstantZero rhs ctx).isSome then some lCmpReg
        else none
      let c0 := RISCVImmediateProperties.mk (IntegerAttr.mk 0 (IntegerType.mk 64))
      match zeroCmpReg with
      | some cmpReg =>
        /- llvm.icmp ne a 0  -> riscv.sltu 0 a (snez) -/
        let (ctx, liOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
          #[] #[] c0 none
        let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk] #[liOp.getResult 0, cmpReg]
          #[] #[] () none
        pure (ctx, #[liOp, retOp], retOp)
      | none =>
        /- llvm.icmp ne lhs rhs  -> riscv.sltu 0 (riscv.xor lhs rhs) -/
        let (ctx, xorOp) ← WfRewriter.createOp! ctx (.riscv .xor) #[RegisterType.mk] #[rCmpReg, lCmpReg]
          #[] #[] () none
        let (ctx, liOp) ← WfRewriter.createOp! ctx (.riscv .li) #[RegisterType.mk] #[]
          #[] #[] c0 none
        let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk] #[liOp.getResult 0, xorOp.getResult 0]
          #[] #[] () none
        pure (ctx, #[xorOp, liOp, retOp], retOp)
    | .slt =>
      /- llvm.icmp slt lhs rhs -> riscv.slt lhs rhs  -/
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .slt) #[RegisterType.mk] #[lCmpReg, rCmpReg]
        #[] #[] () none
      pure (ctx, #[retOp], retOp)
    | .sle =>
      /- llvm.icmp sle lhs rhs -> riscv.xori (riscv_slt rhs lhs) 1 -/
      let (ctx, sltOp) ← WfRewriter.createOp! ctx (.riscv .slt) #[RegisterType.mk] #[rCmpReg, lCmpReg]
        #[] #[] () none
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 none
      pure (ctx, #[sltOp, retOp], retOp)
    | .sgt =>
      /- llvm.icmp sgt lhs rhs -> riscv.slt rhs lhs -/
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .slt) #[RegisterType.mk] #[rCmpReg, lCmpReg]
        #[] #[] () none
      pure (ctx, #[retOp], retOp)
    | .sge =>
      /- llvm.icmp sge lhs rhs -> riscv.xori (riscv_slt lhs rhs) 1 -/
      let (ctx, sltOp) ← WfRewriter.createOp! ctx (.riscv .slt) #[RegisterType.mk] #[lCmpReg, rCmpReg]
        #[] #[] () none
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[sltOp.getResult 0]
        #[] #[] c1 none
      pure (ctx, #[sltOp, retOp], retOp)
    | .ult =>
      /- llvm.icmp ult lhs rhs -> riscv.sltu lhs rhs -/
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk] #[lCmpReg, rCmpReg]
        #[] #[] () none
      pure (ctx, #[retOp], retOp)
    | .ule =>
      /- llvm.icmp ule lhs rhs -> riscv.xori (riscv_sltu rhs lhs) 1 -/
      let (ctx, sltuOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk] #[rCmpReg, lCmpReg]
        #[] #[] () none
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 none
      pure (ctx, #[sltuOp, retOp], retOp)
    | .ugt =>
      /- llvm.icmp ugt lhs rhs -> riscv.sltu rhs lhs -/
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk] #[rCmpReg, lCmpReg]
        #[] #[] () none
      pure (ctx, #[retOp], retOp)
    | .uge =>
      /- llvm.icmp uge lhs rhs -> riscv.xori (riscv_sltu lhs rhs) 1 -/
      let (ctx, sltuOp) ← WfRewriter.createOp! ctx (.riscv .sltu) #[RegisterType.mk] #[lCmpReg, rCmpReg]
        #[] #[] () none
      let c1 := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64))
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .xori) #[RegisterType.mk] #[sltuOp.getResult 0]
        #[] #[] c1 none
      pure (ctx, #[sltuOp, retOp], retOp)
  let (ctx, castEqOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
        #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp] ++ extOps ++ predOps ++ #[castEqOp], #[castEqOp.getResult 0]))

/-- llvm.icmp -> riscv comparison sequence (see `icmp_local`). -/
def icmp (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite icmp_local rewriter op opInBounds

/-- llvm.or -> riscv.or -/
def or_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchOr op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- Actual `riscv.or` -/
  let (ctx, orOp) ← WfRewriter.createOp! ctx (.riscv .or) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOrOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[orOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, orOp, castOrOp], #[castOrOp.getResult 0]))

/-- llvm.or -> riscv.or -/
def or (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite or_local rewriter op opInBounds

/-- llvm.xor -> riscv.xor -/
def xor_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchXor op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- Actual `riscv.xor` -/
  let (ctx, xorOp) ← WfRewriter.createOp! ctx (.riscv .xor) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
      #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castXorOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[xorOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, xorOp, castXorOp], #[castXorOp.getResult 0]))

/-- llvm.xor -> riscv.xor -/
def xor (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite xor_local rewriter op opInBounds

/-- llvm.mul -> riscv.mul -/
def mul_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchMul op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- mulw for i32 (sign-extends result), mul for i64 -/
  let (ctx, mulOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .mulw) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .mul) #[RegisterType.mk] #[rcastOp.getResult 0, lcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, mulOp, castOp], #[castOp.getResult 0]))

/-- llvm.mul -> riscv.mul -/
def mul (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite mul_local rewriter op opInBounds

/-- llvm.sdiv -> riscv.div -/
def sdiv_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSdiv op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- divw for i32, div for i64 -/
  let (ctx, divOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .divw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .div) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[divOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, divOp, castOp], #[castOp.getResult 0]))

/-- llvm.sdiv -> riscv.div -/
def sdiv (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sdiv_local rewriter op opInBounds

/-- llvm.udiv -> riscv.divu -/
def udiv_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchUdiv op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- divuw for i32, divu for i64 -/
  let (ctx, divuOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .divuw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .divu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[divuOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, divuOp, castOp], #[castOp.getResult 0]))

/-- llvm.udiv -> riscv.divu -/
def udiv (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite udiv_local rewriter op opInBounds

/-- llvm.srem -> riscv.rem -/
def srem_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSrem op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- remw for i32, rem for i64 -/
  let (ctx, remOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .remw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .rem) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[remOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, remOp, castOp], #[castOp.getResult 0]))

/-- llvm.srem -> riscv.rem -/
def srem (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite srem_local rewriter op opInBounds

/-- llvm.urem -> riscv.remu -/
def urem_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchUrem op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- remuw for i32, remu for i64 -/
  let (ctx, remuOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .remuw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .remu) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
          #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[remuOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, remuOp, castOp], #[castOp.getResult 0]))

/-- llvm.urem -> riscv.remu -/
def urem (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite urem_local rewriter op opInBounds

/-- llvm.sub -> riscv.sub -/
def sub_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchSub op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- 64-bit sub, or its 32-bit `W` variant for i32 -/
  let (ctx, subOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .subw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .sub) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[subOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, subOp, castOp], #[castOp.getResult 0]))

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
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchSext op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if ¬ isLegalExtOpWidth (opType.bitwidth) then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType retType := type.val | return (ctx, none)
  if retType.bitwidth ≤ opType.bitwidth then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  let (ctx, retOp) ← match opType.bitwidth with
    | 8 =>
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sextb) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () none
      pure (ctx, retOp)
    | 16 =>
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sexth) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () none
      pure (ctx, retOp)
    | 32 =>
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () none
      pure (ctx, retOp)
    | _ =>
      /- unreachable case -/
      return (ctx, none)
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, retOp, castOp], #[castOp.getResult 0]))

/--
  llvm.sext -> riscv.sextb/sexth/sextw (see `sext_local`).
-/
def sext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite sext_local rewriter op opInBounds

/--
  llvm.zext %x `i16` to `i64` -> riscv.zexth %x
  llvm.zext %x `i16` to `i32` -> riscv.zexth %x
  llvm.zext %x `i32` to `i64` -> riscv.zextw %x
-/
def zext_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchZext op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  if ¬ isLegalExtOpWidth (opType.bitwidth) then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType retType := type.val | return (ctx, none)
  if retType.bitwidth ≤ opType.bitwidth then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  let (ctx, retOp) ← match opType.bitwidth with
    | 8 =>
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .zextb) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () none
      pure (ctx, retOp)
    | 16 =>
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .zexth) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () none
      pure (ctx, retOp)
    | 32 =>
      let (ctx, retOp) ← WfRewriter.createOp! ctx (.riscv .zextw) #[RegisterType.mk] #[opCastOp.getResult 0]
        #[] #[] () none
      pure (ctx, retOp)
    | _ =>
      /- unreachable case -/
      return (ctx, none)
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[retOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[opCastOp, retOp, castOp], #[castOp.getResult 0]))

/--
  llvm.zext -> riscv.zexth/zextw (see `zext_local`).
-/
def zext (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite zext_local rewriter op opInBounds

/--
  llvm.trunc %x iX to iY -> builtin_unrealized_conversion_cast (!riscv.reg) : iY
  where `iY`'s width is smaller than `iX`'s.
-/
def trunc_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (operand, _) := matchTrunc op ctx | return (ctx, none)
  let .integerType opType := (operand.getType! ctx.raw).val | return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType retType := type.val | return (ctx, none)
  if opType.bitwidth ≤ retType.bitwidth then return (ctx, none)
  /- First, cast the operand to registers -/
  let (ctx, opCastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[operand]
      #[] #[] () none
  /- Then, cast register to expected output width. -/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[opCastOp.getResult 0]
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
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchShl op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- 64-bit shift-left, or its 32-bit `W` variant for i32 -/
  let (ctx, mulOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .sllw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .sll) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, mulOp, castOp], #[castOp.getResult 0]))

/-- llvm.shl -> riscv.sll -/
def shl (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite shl_local rewriter op opInBounds

/-- llvm.shl -> riscv.srl -/
def lshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs, _) := matchLshr op ctx | return (ctx, none)
  /- support `i64` and `i32` -/
  let .integerType ltype := (lhs.getType! ctx.raw).val | return (ctx, none)
  if ltype.bitwidth ≠ 64 ∧ ltype.bitwidth ≠ 32 then return (ctx, none)
  let .integerType rtype := (rhs.getType! ctx.raw).val | return (ctx, none)
  if rtype.bitwidth ≠ 64 ∧ rtype.bitwidth ≠ 32 then return (ctx, none)
  let type := ((op.getResult 0).get! ctx.raw).type
  let .integerType type' := type.val | return (ctx, none)
  if type'.bitwidth ≠ 64 ∧ type'.bitwidth ≠ 32 then return (ctx, none)
  /- First, cast the operands to registers -/
  let (ctx, lcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[lhs]
      #[] #[] () none
  let (ctx, rcastOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[RegisterType.mk] #[rhs]
      #[] #[] () none
  /- 64-bit logical shift-right, or its 32-bit `W` variant for i32 -/
  let (ctx, mulOp) ←
    if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .srlw) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .srl) #[RegisterType.mk] #[lcastOp.getResult 0, rcastOp.getResult 0]
        #[] #[] () none
  /- Cast back result for type consistency-/
  let (ctx, castOp) ← WfRewriter.createOp! ctx (.builtin .unrealized_conversion_cast) #[type] #[mulOp.getResult 0]
      #[] #[] () none
  some (ctx, some (#[lcastOp, rcastOp, mulOp, castOp], #[castOp.getResult 0]))

/-- llvm.shl -> riscv.srl -/
def lshr (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite lshr_local rewriter op opInBounds

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
      WfRewriter.createOp! ctx (.riscv .sb) #[] #[pcastOp.getResult 0, valcastOp.getResult 0]
        #[] #[] zero none
    else if type'.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .sw) #[] #[pcastOp.getResult 0, valcastOp.getResult 0]
        #[] #[] zero none
    else
      WfRewriter.createOp! ctx (.riscv .sd) #[] #[pcastOp.getResult 0, valcastOp.getResult 0]
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
      if scale &&& (scale - 1) == 0 then
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
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
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
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchSmax op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  /- For i32, sign-extend before max so negative values compare correctly. -/
  if t.bitwidth = 32 then
    let (ctx, ls) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[lCastOp.getResult 0]
        #[] #[] () none
    let (ctx, rs) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[rCastOp.getResult 0]
        #[] #[] () none
    let (ctx, maxOp) ← WfRewriter.createOp! ctx (.riscv .max) #[RegisterType.mk]
        #[ls.getResult 0, rs.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (maxOp.getResult 0)
    some (ctx, some (#[lCastOp, rCastOp, ls, rs, maxOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, maxOp) ← WfRewriter.createOp! ctx (.riscv .max) #[RegisterType.mk] #[lCastOp.getResult 0, rCastOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (maxOp.getResult 0)
    some (ctx, some (#[lCastOp, rCastOp, maxOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.smax -> riscv.max -/
def smax (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite smax_local rewriter op opInBounds

/-- llvm.intr.smin -> riscv.min -/
def smin_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchSmin op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  /- For i32, sign-extend before min so negative values compare correctly. -/
  if t.bitwidth = 32 then
    let (ctx, ls) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[lCastOp.getResult 0]
        #[] #[] () none
    let (ctx, rs) ← WfRewriter.createOp! ctx (.riscv .sextw) #[RegisterType.mk] #[rCastOp.getResult 0]
        #[] #[] () none
    let (ctx, minOp) ← WfRewriter.createOp! ctx (.riscv .min) #[RegisterType.mk]
        #[ls.getResult 0, rs.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (minOp.getResult 0)
    some (ctx, some (#[lCastOp, rCastOp, ls, rs, minOp, castBackOp], #[castBackOp.getResult 0]))
  else
    let (ctx, minOp) ← WfRewriter.createOp! ctx (.riscv .min) #[RegisterType.mk] #[lCastOp.getResult 0, rCastOp.getResult 0]
        #[] #[] () none
    let (ctx, castBackOp) ← replaceWithRegLocal ctx op (minOp.getResult 0)
    some (ctx, some (#[lCastOp, rCastOp, minOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.smin -> riscv.min -/
def smin (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite smin_local rewriter op opInBounds

/-- llvm.intr.umax -> riscv.maxu -/
def umax_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchUmax op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let (ctx, maxuOp) ← WfRewriter.createOp! ctx (.riscv .maxu) #[RegisterType.mk] #[lCastOp.getResult 0, rCastOp.getResult 0]
      #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (maxuOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, maxuOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.umax -> riscv.maxu -/
def umax (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite umax_local rewriter op opInBounds

/-- llvm.intr.umin -> riscv.minu -/
def umin_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (lhs, rhs) := matchUmin op ctx | return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, lCastOp) ← castToRegLocal ctx lhs
  let (ctx, rCastOp) ← castToRegLocal ctx rhs
  let (ctx, minuOp) ← WfRewriter.createOp! ctx (.riscv .minu) #[RegisterType.mk] #[lCastOp.getResult 0, rCastOp.getResult 0]
      #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (minuOp.getResult 0)
  some (ctx, some (#[lCastOp, rCastOp, minuOp, castBackOp], #[castBackOp.getResult 0]))

/-- llvm.intr.umin -> riscv.minu -/
def umin (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) :=
  RewritePattern.fromLocalRewrite umin_local rewriter op opInBounds

/-- llvm.intr.fshl with identical data operands is a rotate-left: -> riscv.rol.
    The general (distinct-operand) funnel shift is left unselected. -/
def fshl_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshl op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  let (ctx, amtCastOp) ← castToRegLocal ctx amt
  let (ctx, rolOp) ←
    if t.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .rolw) #[RegisterType.mk] #[valCastOp.getResult 0, amtCastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .rol) #[RegisterType.mk] #[valCastOp.getResult 0, amtCastOp.getResult 0]
          #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (rolOp.getResult 0)
  some (ctx, some (#[valCastOp, amtCastOp, rolOp, castBackOp], #[castBackOp.getResult 0]))

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

/-- llvm.intr.fshr with identical data operands is a rotate-right: -> riscv.ror.
    The general (distinct-operand) funnel shift is left unselected. -/
def fshr_local (ctx : WfIRContext OpCode) (op : OperationPtr) :
    Option (WfIRContext OpCode × Option (Array OperationPtr × Array ValuePtr)) := do
  let some (a, b, amt) := matchFshr op ctx | return (ctx, none)
  if a ≠ b then return (ctx, none)
  let .integerType t := ((op.getResult 0).get! ctx.raw).type.val | return (ctx, none)
  if t.bitwidth ≠ 64 ∧ t.bitwidth ≠ 32 then return (ctx, none)
  let (ctx, valCastOp) ← castToRegLocal ctx a
  let (ctx, amtCastOp) ← castToRegLocal ctx amt
  let (ctx, rorOp) ←
    if t.bitwidth = 32 then
      WfRewriter.createOp! ctx (.riscv .rorw) #[RegisterType.mk] #[valCastOp.getResult 0, amtCastOp.getResult 0]
          #[] #[] () none
    else
      WfRewriter.createOp! ctx (.riscv .ror) #[RegisterType.mk] #[valCastOp.getResult 0, amtCastOp.getResult 0]
          #[] #[] () none
  let (ctx, castBackOp) ← replaceWithRegLocal ctx op (rorOp.getResult 0)
  some (ctx, some (#[valCastOp, amtCastOp, rorOp, castBackOp], #[castBackOp.getResult 0]))

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
    sdiv, udiv, srem, urem, sext, zext, trunc, shl, lshr, sub, load, getelementptr, store,
    smax, smin, umax, umin, saddSat, ssubSat, uaddSat, usubSat, sshlSat, ushlSat, abs,
    fshlConst, fshrConst, fshl, fshr, poisonConst, freeze]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying pattern rewrites"
  | some ctx => pure ctx

public def IselRISCV64 : Pass OpCode :=
  { name := "isel-riscv64"
    description :=
      "Lower LLVM IR to RISCV 64 assembly instruction selection pass."
    run := ISelPass.impl }
