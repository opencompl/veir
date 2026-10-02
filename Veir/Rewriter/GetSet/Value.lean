module

public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.Rewriter.WfRewriter.GetSetTactic

public section

/-
The getters we consider are:
* BlockPtr.get! optionally replaced by the following special cases:
  * Block.firstUse
  * Block.prev
  * Block.next
  * Block.parent
  * Block.firstOp
  * Block.lastOp
* OperationPtr.get! optionally replaced by the following special cases:
  * Operation.prev
  * Operation.next
  * Operation.parent
  * OperationPtr.getOpType!
  * Operation.attrs
* OperationPtr.getProperties!
* OperationPtr.getNumResults!
* OpResultPtr.get!
* OperationPtr.getNumOperands!
* OpOperandPtr.get! optionally replaced by the following special case:
* OperationPtr.getOperands!
* OperationPtr.getNumSuccessors!
* BlockOperandPtr.get!
* OperationPtr.getSuccessor!
* OperationPtr.getSuccessors!
* OperationPtr.getNumRegions!
* OperationPtr.getRegion!
* BlockOperandPtrPtr.get!
* BlockPtr.getNumArguments!
* BlockArgumentPtr.get!
* RegionPtr.get! with optionally special cases for:
  * firstBlock
  * lastBlock
  * parent
* ValuePtr.getFirstUse!
* ValuePtr.getType!
* OpOperandPtrPtr.get!
-/

namespace Veir

variable {OpInfo} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode : Dialect}
/-! ## `Rewriter.setType` -/

section Rewriter.setType

variable {value : ValuePtr}

attribute [local grind] Rewriter.setType

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstUse!_setType {block : BlockPtr} :
    block.getFirstUse! (Rewriter.setType ctx value newType valueIn) = block.getFirstUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getPrevBlock!_setType {block : BlockPtr} :
    block.getPrevBlock! (Rewriter.setType ctx value newType valueIn) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNextBlock!_setType {block : BlockPtr} :
    block.getNextBlock! (Rewriter.setType ctx value newType valueIn) = block.getNextBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getParent!_setType {block : BlockPtr} :
    block.getParent! (Rewriter.setType ctx value newType valueIn) = block.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getFirstOp!_setType {block : BlockPtr} :
    block.getFirstOp! (Rewriter.setType ctx value newType valueIn) = block.getFirstOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getLastOp!_setType {block : BlockPtr} :
    block.getLastOp! (Rewriter.setType ctx value newType valueIn) = block.getLastOp! ctx := by
  grind

@[grind =, simp_getset]
theorem OperationPtr.getRegions!_setType {operation : OperationPtr} :
    operation.getRegions! (Rewriter.setType ctx value newType valueIn) = match value with | ValuePtr.opResult _ => operation.getRegions! ctx | ValuePtr.blockArgument _ => operation.getRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getPrevOp!_setType {operation : OperationPtr} :
    operation.getPrevOp! (Rewriter.setType ctx value newType valueIn) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNextOp!_setType {operation : OperationPtr} :
    operation.getNextOp! (Rewriter.setType ctx value newType valueIn) = operation.getNextOp! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getParent!_setType {operation : OperationPtr} :
    operation.getParent! (Rewriter.setType ctx value newType valueIn) = operation.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOpType!_setType {operation : OperationPtr} :
    operation.getOpType! (Rewriter.setType ctx value newType valueIn) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getAttributes!_setType {operation : OperationPtr} :
    operation.getAttributes! (Rewriter.setType ctx value newType valueIn) = operation.getAttributes! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getProperties!_setType {operation : OperationPtr} :
    operation.getProperties! (Rewriter.setType ctx value newType valueIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumResults!_setType {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumResults! ctx := by
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getOwner!_setType {opResult : OpResultPtr} :
    opResult.getOwner! (Rewriter.setType ctx value newType valueIn) = opResult.getOwner! ctx := by
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getIndex!_setType {opResult : OpResultPtr} :
    opResult.getIndex! (Rewriter.setType ctx value newType valueIn) = opResult.getIndex! ctx := by
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getFirstUse!_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (Rewriter.setType ctx value newType valueIn) = opResult.getFirstUse! ctx := by
  grind

@[grind =, simp_getset]
theorem OpResultPtr.getType!_setType {opResult : OpResultPtr} :
    opResult.getType! (Rewriter.setType ctx value newType valueIn) = if value = ValuePtr.opResult opResult then newType else opResult.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumOperands!_setType {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getValue!_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (Rewriter.setType ctx value newType valueIn) = opOperand.getValue! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getOwner!_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (Rewriter.setType ctx value newType valueIn) = opOperand.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getBack!_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (Rewriter.setType ctx value newType valueIn) = opOperand.getBack! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtr.getNextUse!_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (Rewriter.setType ctx value newType valueIn) = opOperand.getNextUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getOperands!_setType {operation : OperationPtr} :
    operation.getOperands! (Rewriter.setType ctx value newType valueIn) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumSuccessors!_setType {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getValue!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (Rewriter.setType ctx value newType valueIn) = blockOperand.getValue! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getOwner!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (Rewriter.setType ctx value newType valueIn) = blockOperand.getOwner! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getBack!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (Rewriter.setType ctx value newType valueIn) = blockOperand.getBack! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtr.getNextUse!_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (Rewriter.setType ctx value newType valueIn) = blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessor!_setType {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.setType ctx value newType valueIn) index =
    operation.getSuccessor! ctx index := by
  simp only [OperationPtr.getSuccessor!_def, ← BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getSuccessors!_setType {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.setType ctx value newType valueIn) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =, simp_getset]
theorem OperationPtr.getNumRegions!_setType {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.setType ctx value newType valueIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OperationPtr.getRegion!_setType {operation : OperationPtr} :
    operation.getRegion! (Rewriter.setType ctx value newType valueIn) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockOperandPtrPtr.get!_setType {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.setType ctx value newType valueIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem BlockPtr.getNumArguments!_setType {block : BlockPtr} :
    block.getNumArguments! (Rewriter.setType ctx value newType valueIn) =
    block.getNumArguments! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getOwner!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (Rewriter.setType ctx value newType valueIn) = blockArg.getOwner! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getIndex!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (Rewriter.setType ctx value newType valueIn) = blockArg.getIndex! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getFirstUse!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (Rewriter.setType ctx value newType valueIn) = blockArg.getFirstUse! ctx := by
  grind

@[grind =, simp_getset]
theorem BlockArgumentPtr.getType!_setType {blockArg : BlockArgumentPtr} :
    blockArg.getType! (Rewriter.setType ctx value newType valueIn) = if value = ValuePtr.blockArgument blockArg then newType else blockArg.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getLastBlock!_setType {region : RegionPtr} :
    region.getLastBlock! (Rewriter.setType ctx value newType valueIn) = region.getLastBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getFirstBlock!_setType {region : RegionPtr} :
    region.getFirstBlock! (Rewriter.setType ctx value newType valueIn) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem RegionPtr.getParent!_setType {region : RegionPtr} :
    region.getParent! (Rewriter.setType ctx value newType valueIn) = region.getParent! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem ValuePtr.getFirstUse!_setType {value' : ValuePtr} :
    value'.getFirstUse! (Rewriter.setType ctx value newType valueIn) =
    value'.getFirstUse! ctx := by
  grind

@[grind =, simp_getset]
theorem ValuePtr.getType!_setType {value' : ValuePtr} :
    value'.getType! (Rewriter.setType ctx value newType valueIn) =
    if value = value' then newType else value'.getType! ctx := by
  grind

@[simp, grind =, simp_getset]
theorem OpOperandPtrPtr.get!_setType {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.setType ctx value newType valueIn) =
    opOperandPtr.get! ctx := by
  grind

end Rewriter.setType

end Veir
