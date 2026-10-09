module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic


public section

namespace Veir

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
theorem BlockPtr.prev!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).prev = (block.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).next = (block.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).parent = (block.get! ctx).parent := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem BlockPtr.firstOp!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).firstOp =
    (block.get! ctx).firstOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem BlockPtr.lastOp!_detachBlockOperands_loop {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).lastOp =
    (block.get! ctx).lastOp := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.prev!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).prev =
    (operation.get! ctx).prev := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.next!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).next =
    (operation.get! ctx).next := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[grind =, simp_getset]
theorem OperationPtr.parent!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).parent =
    (operation.get! ctx).parent := by
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
theorem OperationPtr.attrs!_detachBlockOperands_loop {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex)).attrs =
    (operation.get! ctx).attrs := by
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
theorem OpResultPtr.get!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_detachBlockOperands_loop {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachBlockOperands_loop {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) = operation.getNumOperands! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.get!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_detachBlockOperands_loop {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.get!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.get! ctx := by
  induction idx generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_detachBlockOperands_loop {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.detachBlockOperands.loop ctx op' idx hCtx hOp hIdx) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_detachBlockOperands_loop {region : RegionPtr} :
    region.get! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    region.get! ctx := by
  induction index generalizing ctx
  · grind [Rewriter.detachBlockOperands.loop]
  · simp only [Rewriter.detachBlockOperands.loop]
    grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachBlockOperands_loop {region : RegionPtr} :
    region.getParent! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachBlockOperands_loop {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachBlockOperands_loop {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachBlockOperands.loop ctx op' index hCtx hOp hIndex) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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
theorem BlockPtr.prev!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).prev = (block.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.next!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).next = (block.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.parent!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).parent = (block.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.firstOp!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.lastOp!_detachBlockOperands {block : BlockPtr} :
    (block.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.prev!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.next!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.parent!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_detachBlockOperands {operation : OperationPtr} :
    operation.getOpType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.attrs!_detachBlockOperands {operation : OperationPtr} :
    (operation.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp)).attrs =
    (operation.get! ctx).attrs := by
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
theorem OpResultPtr.get!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getIndex!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getType!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpResultPtr.getOwner!_detachBlockOperands {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_detachBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.detachBlockOperands ctx op' hCtx hOp) = operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.get!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_detachBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.get!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getType!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getLoc!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_detachBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.get!_detachBlockOperands {region : RegionPtr} :
    region.get! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    region.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_detachBlockOperands {region : RegionPtr} :
    region.getParent! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_detachBlockOperands {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_detachBlockOperands {region : RegionPtr} :
    region.getLastBlock! (Rewriter.detachBlockOperands ctx op' hCtx hOp) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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
