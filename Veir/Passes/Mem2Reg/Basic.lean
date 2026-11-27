module

public import Veir.Rewriter.WfRewriter
public import Veir.GlobalOpInfo

import Veir.Interfaces.ConstantLikeInterfaces
import Veir.Interfaces.RegionKindInterfaces

/-!
# Scalar allocation promotion

Promote integer allocas of one element in a single block, with direct,
nonvolatile accesses matching the allocated type. Under the current memory
model, checking the pointer's uses does not rule out accesses through other
pointers. Correctness also requires a justification for removing the allocation.
-/

public section

namespace Veir.Mem2Reg

private def blockOperations (ctx : IRContext OpCode) (block : BlockPtr) :
    Array OperationPtr := Id.run do
  let mut result := #[]
  let mut next := block.getFirstOp! ctx
  while let some op := next do
    result := result.push op
    next := op.getNextOp! ctx
  return result

/-- Check an entry-block allocation and its direct load/store uses in the same
region and return the entry block. Initialisation is checked separately. -/
private def analyseSlot? (ctx : WfIRContext OpCode) (region : RegionPtr)
    (allocation : OperationPtr) : Option BlockPtr := do
  guard (region.InBounds ctx.raw ∧ allocation.InBounds ctx.raw)
  guard (region.hasSSADominance ctx)
  let block ← region.getFirstBlock! ctx.raw
  guard (allocation.getParent! ctx.raw = some block)
  guard (allocation.getOpType! ctx.raw = .llvm .alloca)
  guard (allocation.getNumOperands! ctx.raw = 1 ∧ allocation.getNumResults! ctx.raw = 1)
  let properties := allocation.getProperties! ctx.raw Llvm.alloca
  guard (!properties.inalloca)
  let .integerType type := properties.elem_type.val | none
  guard ([8, 16, 32, 64].contains type.bitwidth)
  let some (.int _ (.val count)) :=
    (allocation.getOperand! ctx.raw 0).constantValue ctx.raw | none
  guard (count.toNat = 1)
  let pointer : ValuePtr := allocation.getResult 0
  let mut next := pointer.getFirstUse! ctx.raw
  while let some use := next do
    let owner := use.getOwner! ctx.raw
    guard (owner.getParentRegion! ctx.raw = some region)
    match owner.getOpType! ctx.raw with
    | .llvm .load =>
      guard (use.index = 0 ∧ owner.getOperands! ctx.raw = #[pointer])
      guard (owner.getResultTypes! ctx.raw = #[properties.elem_type])
      let load := owner.getProperties! ctx.raw Llvm.load
      guard (!load.volatile_ ∧ load.syncscope.isNone)
    | .llvm .store =>
      guard (use.index = 1 ∧ owner.getNumOperands! ctx.raw = 2)
      guard ((owner.getOperand! ctx.raw 0).getType! ctx.raw = properties.elem_type)
      let store := owner.getProperties! ctx.raw Llvm.store
      guard (!store.volatile_ ∧ store.syncscope.isNone)
    | _ => none
    next := use.getNextUse! ctx.raw
  return block

/-- Check the single-block restrictions and collect the operations before
forwarding erases any loads. Each load from the allocation must follow a store. -/
private def singleBlockOperations? (ctx : WfIRContext OpCode) (block : BlockPtr)
    (pointer : ValuePtr) : Option (Array OperationPtr) := do
  guard (block.getNextBlock! ctx.raw = none)
  let operations := blockOperations ctx.raw block
  let mut initialised := false
  for op in operations do
    guard (op.getNumRegions! ctx.raw = 0 ∧ op.getNumSuccessors! ctx.raw = 0)
    let opType := op.getOpType! ctx.raw
    guard ((HasOpInfo.callOpInterface? opType).isNone)
    -- Intrinsic calls do not implement the ordinary call interface.
    guard (opType ≠ .llvm .call_intrinsic)
    match opType with
    | .llvm .store =>
      if op.getOperand! ctx.raw 1 = pointer then initialised := true
    | .llvm .load =>
      if op.getOperand! ctx.raw 0 = pointer then guard initialised
    | _ => pure ()
  guard initialised
  return operations

/-- Forward loads from the incoming value or the most recent store, and return
the value available at block exit. Read store operands from the updated context,
since they may refer to an earlier load. -/
private def forwardBlock (ctx : WfIRContext OpCode) (pointer : ValuePtr)
    (operations : Array OperationPtr) (incoming : Option ValuePtr) :
    Option (WfIRContext OpCode × Option ValuePtr) := do
  let mut ctx := ctx
  let mut current := incoming
  for op in operations do
    match op.getOpType! ctx.raw with
    | .llvm .store =>
      if op.getOperand! ctx.raw 1 = pointer then
        current := some (op.getOperand! ctx.raw 0)
    | .llvm .load =>
      if op.getOperand! ctx.raw 0 = pointer then
        let value ← current
        ctx := WfRewriter.replaceValue! ctx (op.getResult 0) value
        ctx := WfRewriter.eraseOp! ctx op
    | _ => pure ()
  return (ctx, current)

/-- Remove the remaining stores and the allocation. Collect the stores before
erasing them, since erasure changes the pointer's use list. -/
private def eraseSlot? (ctx : WfIRContext OpCode) (allocation : OperationPtr) :
    Option (WfIRContext OpCode) := do
  let pointer : ValuePtr := allocation.getResult 0
  let mut stores := #[]
  let mut next := pointer.getFirstUse! ctx.raw
  while let some use := next do
    let owner := use.getOwner! ctx.raw
    guard (owner.getOpType! ctx.raw = .llvm .store ∧ use.index = 1)
    stores := stores.push owner
    next := use.getNextUse! ctx.raw
  let mut ctx := ctx
  for store in stores do
    ctx := WfRewriter.eraseOp! ctx store
  return WfRewriter.eraseOp! ctx allocation

/-- Promote one initialised i8/i16/i32/i64 allocation in a single-block SSACFG
region with no calls, successors or nested regions. The input must be verified.
Return a changed flag with the context, or `none` if forwarding or cleanup fails.
Unsupported allocations, uses or block shapes return `(false, ctx)`. -/
def promoteSingleBlock? (ctx : WfIRContext OpCode) (region : RegionPtr)
    (allocation : OperationPtr) : Option (Bool × WfIRContext OpCode) := do
  let some block := analyseSlot? ctx region allocation | return (false, ctx)
  let pointer : ValuePtr := allocation.getResult 0
  let some operations := singleBlockOperations? ctx block pointer | return (false, ctx)
  let (ctx, _) ← forwardBlock ctx pointer operations none
  let ctx ← eraseSlot? ctx allocation
  return (true, ctx)

end Veir.Mem2Reg
