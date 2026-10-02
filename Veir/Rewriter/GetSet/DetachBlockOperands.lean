module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic

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

fold_field_getters_in_grind

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
section Rewriter.detachBlockOperands.loop

variable {op : OperationPtr}

attribute [local grind] Rewriter.detachBlockOperands.loop

-- The theorem `BlockPtr.firstUse!_detachBlockOperands_loop` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_detachBlockOperands_loop {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = block.getPrevBlock! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_detachBlockOperands_loop {block : BlockPtr} :
    block.getNextBlock! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = block.getNextBlock! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_detachBlockOperands_loop {block : BlockPtr} :
    block.getParent! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = block.getParent! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem BlockPtr.getFirstOp!_detachBlockOperands_loop {block : BlockPtr} :
    block.getFirstOp! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = block.getFirstOp! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem BlockPtr.getLastOp!_detachBlockOperands_loop {block : BlockPtr} :
    block.getLastOp! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = block.getLastOp! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.getPrevOp!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getPrevOp! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.getNextOp!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNextOp! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.getParent!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getParent! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getParent! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOpType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getAttributes! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) opCode =
    operation.getProperties! ctx opCode := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumResults! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNumOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) i =
    operation.getSuccessor! ctx i := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop, OperationPtr.getSuccessor!_def]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind [OperationPtr.getSuccessor!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_detachBlockOperands_loop,
    OperationPtr.getNumSuccessors!_detachBlockOperands_loop]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    operation.getNumRegions! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_detachBlockOperands_loop {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    block.getNumArguments! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachBlockOperands_loop {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachBlockOperands_loop {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachBlockOperands_loop {region : RegionPtr} :
    region.getParent! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_detachBlockOperands_loop {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getFirstUse! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getType!_detachBlockOperands_loop {value : ValuePtr} :
    value.getType! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    value.getType! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
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

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_detachBlockOperands {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_detachBlockOperands {block : BlockPtr} :
    block.getNextBlock! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_detachBlockOperands {block : BlockPtr} :
    block.getParent! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = block.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_detachBlockOperands {block : BlockPtr} :
    block.getFirstOp! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = block.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_detachBlockOperands {block : BlockPtr} :
    block.getLastOp! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = block.getLastOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_detachBlockOperands {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_detachBlockOperands {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_detachBlockOperands {operation : OperationPtr} :
    operation.getParent! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachBlockOperands {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_detachBlockOperands {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_detachBlockOperands {operation : OperationPtr} :
    operation.getProperties! (Rewriter.detachBlockOperands ctx op' hCtx hOp) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_detachBlockOperands {operation : OperationPtr} :
    operation.getOperands! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getOperands! ctx := by
  simp only [Rewriter.detachBlockOperands]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumSuccessors! ctx := by
  grind

-- The theorem `BlockOperandPtr.get!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_detachBlockOperands {operation : OperationPtr} :
    operation.getRegion! (Rewriter.detachBlockOperands ctx op' hCtx hOp) i =
    operation.getRegion! ctx i := by
  grind

-- The theorem `BlockOperandPtrPtr.get!_detachBlockOperands` is missing because it is quite complex to state.
-- In any case, we shouldn't need it in practice, as we should reason at a higher-level abstraction at
-- this point, likely on `BlockPtr.DefUse` directly.

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_detachBlockOperands {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.detachBlockOperands ctx op' hCtx hOp) i =
    operation.getSuccessor! ctx i := by
  grind [OperationPtr.getSuccessor!_def, Rewriter.detachBlockOperands]

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_detachBlockOperands {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getSuccessors! ctx := by
  simp only [OperationPtr.getSuccessors!_def, OperationPtr.getSuccessor!_detachBlockOperands,
    OperationPtr.getNumSuccessors!_detachBlockOperands]

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_detachBlockOperands {block : BlockPtr} :
    block.getNumArguments! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachBlockOperands {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachBlockOperands {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachBlockOperands {region : RegionPtr} :
    region.getParent! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_detachBlockOperands {value : ValuePtr} :
    value.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
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
