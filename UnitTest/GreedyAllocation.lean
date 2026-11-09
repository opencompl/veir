module

import Veir.Interpreter.Memory
import Veir.GlobalOpInfo
import Veir.PatternRewriter.Basic
meta import Veir.GlobalOpInfo
meta import Veir.PatternRewriter.Basic
meta import Veir.Dialects.LLVM.OpInfo
import all Veir.PatternRewriter.Basic

open Veir

/-!
Regression for the allocation exclusion in dead-code erasure: an unused first allocation still
changes the address returned by a later allocation. These addresses are observable through pointer
operations in the deterministic memory model.
-/

private def allocateAddress (memory : MemoryState) (size : UInt64) : Option (MemoryState × UInt64) :=
  match memory.alloc size with
  | .ok (next, pointer) => some (next, pointer.address)
  | _ => none

private def addressKeepingUnusedAllocation : Option UInt64 := do
  let (memory, _) ← allocateAddress .empty 4
  let (_, address) ← allocateAddress memory 4
  pure address

private def addressErasingUnusedAllocation : Option UInt64 :=
  (allocateAddress .empty 4).map (·.2)

#guard addressKeepingUnusedAllocation = some 65552
#guard addressErasingUnusedAllocation = some 65536
#guard addressKeepingUnusedAllocation ≠ addressErasingUnusedAllocation

/- The old effects-only deadness checks admit alloca: no writes, and no terminator action.
Its allocation effect distinguishes it from the permitted erasure obligation. -/
#guard (OpCode.getEffects (.llvm .alloca) (default : AllocaProperties)).writes = false
#guard (OpCode.getEffects (.llvm .alloca) (default : AllocaProperties)).allocates = true
#guard HasOpInfo.isTerminator (OpCode.llvm .alloca) = false


/-- Two unused LLVM allocations with a shared constant count, attached to a real worklist block. -/
private def allocationFixture : WfIRContext OpCode × OperationPtr × OperationPtr := Id.run do
  let (ctx, moduleOp) := WfIRContext.create! OpCode
  let block := ((moduleOp.getRegion! ctx.raw 0).getFirstBlock! ctx.raw).get!
  let i64 : TypeAttr := IntegerType.signless 64
  let constant : LLVMConstantProperties := { value := .integer (IntegerAttr.mk 1 (IntegerType.signless 64)) }
  let (ctx, count) := (WfRewriter.createOp! ctx Llvm.mlir__constant #[i64] #[] #[] #[] constant
    (some (.atEnd block))).get!
  let properties : AllocaProperties :=
    { inalloca := false, elem_type := IntegerType.signless 32,
      alignment := IntegerAttr.mk 0 (IntegerType.signless 64) }
  let (ctx, first) := (WfRewriter.createOp! ctx Llvm.alloca #[LLVM.PointerType.mk]
    #[count.getResult 0] #[] #[] properties (some (.atEnd block))).get!
  let (ctx, second) := (WfRewriter.createOp! ctx Llvm.alloca #[LLVM.PointerType.mk]
    #[count.getResult 0] #[] #[] properties (some (.atEnd block))).get!
  return (ctx, first, second)

private def noMatchPattern : RewritePattern OpCode :=
  fun rewriter _ _ => some { rewriter with hasDoneAction := false }

/-- Automatic DCE must dispatch an unused allocator to the ordinary pattern arm. Both allocations
remain in bounds after each concrete worklist step, and neither step reports an action. -/
private def allocationGuardRegression : Bool := Id.run do
  let (ctx, first, second) := allocationFixture
  if !(decide (first.isTriviallyDead ctx.raw) && decide (second.isTriviallyDead ctx.raw)) then
    return false
  let before : PatternRewriter OpCode :=
    { ctx, hasDoneAction := false, worklist := PatternRewriter.Worklist.empty.push first |>.push second }
  let some afterSecond := noMatchPattern.worklistStep before | return false
  if afterSecond.hasDoneAction || !(decide (first.InBounds afterSecond.ctx.raw)) ||
      !(decide (second.InBounds afterSecond.ctx.raw)) then
    return false
  let some afterFirst := noMatchPattern.worklistStep afterSecond | return false
  return !afterFirst.hasDoneAction && decide (first.InBounds afterFirst.ctx.raw) &&
    decide (second.InBounds afterFirst.ctx.raw) && afterFirst.worklist.isEmpty

#guard allocationGuardRegression
