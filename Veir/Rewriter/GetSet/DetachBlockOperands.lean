module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic

import Veir.Rewriter.LinkedList.GetSet
import Veir.ForLean
import Veir.IR.DeallocLemmas

public section

/-
 - The getters we consider are:
 - * BlockPtr.get! optionally replaced by the following special cases:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! optionally replaced by the following special cases:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * OperationPtr.getOpType!
 -   * Operation.attrs
 - * OperationPtr.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getOperands!
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getSuccessor!
 - * OperationPtr.getSuccessors!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! with optionally special cases for:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
section Rewriter.detachBlockOperands.loop

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachBlockOperands.loop

-- The theorem `BlockPtr.firstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.prev!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).prev = (block.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.next!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).next = (block.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem BlockPtr.parent!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).parent = (block.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem BlockPtr.firstOp!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).firstOp =
    (block.get! ctx).firstOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem BlockPtr.lastOp!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).lastOp =
    (block.get! ctx).lastOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem OperationPtr.prev!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).prev =
    (operation.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem OperationPtr.next!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).next =
    (operation.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =]
theorem OperationPtr.parent!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).parent =
    (operation.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getOpType!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOpType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).attrs =
    (operation.get! ctx).attrs := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) opCode =
    operation.getProperties! ctx opCode := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumResults! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OpResultPtr.get!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNumOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getOperands!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumSuccessors! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

-- The theorem `BlockOperandPtr.getFirstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem OperationPtr.getSuccessor!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getSuccessor! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop, OperationPtr.getSuccessor!_def]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_detachBlockOperands_loop,
    OperationPtr.getNumSuccessors!_detachBlockOperands_loop]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumRegions! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getRegion! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

-- The theorem `BlockOperandPtrPtr.getFirstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachBlockOperands_loop {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    block.getNumArguments! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem RegionPtr.get!_detachBlockOperands_loop {region : RegionPtr} :
    region.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    region.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachBlockOperands_loop {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getFirstUse! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem ValuePtr.getType!_detachBlockOperands_loop {value : ValuePtr} :
    value.getType! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_detachBlockOperands_loop {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    opOperandPtr.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

end Rewriter.detachBlockOperands.loop
section Rewriter.detachBlockOperands

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachBlockOperands

-- The theorem `BlockPtr.firstUse!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem BlockPtr.prev!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_detachBlockOperands {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_detachBlockOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachBlockOperands ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_detachBlockOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getOperands! ctx := by
  simp only [Rewriter.detachBlockOperands]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

-- The theorem `BlockOperandPtr.get!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem OperationPtr.getNumRegions!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_detachBlockOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachBlockOperands ctx op' hCtx hOp) i =
    operation.getRegion! ctx i := by
  grind

-- The theorem `BlockOperandPtrPtr.get!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =]
theorem OperationPtr.getSuccessor!_detachBlockOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachBlockOperands ctx op' hCtx hOp) i =
    operation.getSuccessor! ctx i := by
  grind [OperationPtr.getSuccessor!_def, Rewriter.detachBlockOperands]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_detachBlockOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_detachBlockOperands,
    OperationPtr.getNumSuccessors!_detachBlockOperands]

@[simp, grind =]
theorem BlockPtr.getNumArguments!_detachBlockOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_detachBlockOperands {region : RegionPtr} :
    region.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_detachBlockOperands {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_detachBlockOperands {value : ValuePtr} :
    value.getType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    value.getType! ctx := by
  grind

theorem OpOperandPtrPtr.get!_detachBlockOperands {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.detachBlockOperands

end Veir
