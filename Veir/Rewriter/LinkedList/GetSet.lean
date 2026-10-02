module

public import Veir.Rewriter.LinkedList.Basic
import all Veir.Rewriter.LinkedList.Basic

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
 -   * Operation.attrs
 -   * Operation.properties
 - * OperationPtr.getOpType!
 - * OperationPtr.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getOperands!
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! optionally replaced by the following special cases:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/
namespace Veir

fold_field_getters_in_grind

variable {op op' operation operation' : OperationPtr}
variable {block block' : BlockPtr}
variable {rg rg' : RegionPtr}
variable {opOperand opOperand' : OpOperandPtr}
variable {opOperandPtr opOperandPtr' : OpOperandPtrPtr}
variable {blockOperand blockOperand' : BlockOperandPtr}
variable {value value' : ValuePtr}
variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : IRContext OpInfo}
variable {Dialect : Type} [HasOpInfo Dialect] [HasDialect OpInfo Dialect]
variable {opCode propT : Dialect}

/- OpOperandPtr.removeFromCurrent -/
attribute [local grind] OpOperandPtr.removeFromCurrent

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getPrevBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getNextBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getParent! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getLastOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getPrevOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNextOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getParent! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.getOpType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)) =
    (operation.getOpType! ctx) := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getAttributes! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getProperties! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) propT =
    operation.getProperties! ctx propT := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumResults! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[grind =]
theorem OpResultPtr.getIndex!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getIndex! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.getBack! ctx) = .valueFirstUse (.opResult opResult) then ((opOperand'.getNextUse! ctx)) else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =]
theorem OpResultPtr.getType!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [removeFromCurrent]
  split <;> grind

@[grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [removeFromCurrent]
  split <;> grind

@[grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = (if (opOperand'.getNextUse! ctx) = some opOperand then (opOperand'.getBack! ctx) else opOperand.getBack! ctx) := by
  simp only [removeFromCurrent]
  split <;> grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = (if (opOperand'.getBack! ctx) = .operandNextUse opOperand then (opOperand'.getNextUse! ctx) else opOperand.getNextUse! ctx) := by
  simp only [removeFromCurrent]
  split <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getOperands! ctx := by
  simp only [OpOperandPtr.removeFromCurrent]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumRegions! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getRegion! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_removeFromCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.removeFromCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.getBack! ctx) = .valueFirstUse (.blockArgument blockArg) then ((opOperand'.getNextUse! ctx)) else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getLastBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = region.getLastBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getFirstBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getParent! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = region.getParent! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.getBack! ctx) = .valueFirstUse value then
      (opOperand'.getNextUse! ctx)
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if opOperandPtr = (opOperand'.getBack! ctx) then
      (opOperand'.getNextUse! ctx)
    else
      opOperandPtr.get! ctx := by
  grind

/- OpOperandPtr.insertIntoCurrent -/
attribute [local grind] OpOperandPtr.insertIntoCurrent

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getPrevBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getNextBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getParent! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getLastOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getPrevOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNextOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getParent! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getOpType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getAttributes! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getProperties! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumResults! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[grind =]
theorem OpResultPtr.getIndex!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getIndex! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.getValue! ctx) = (.opResult opResult) then (opOperand' : Option OpOperandPtr) else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =]
theorem OpResultPtr.getType!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [insertIntoCurrent]
  split <;> grind

@[grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [insertIntoCurrent]
  split <;> grind

@[grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = (if (opOperand'.getValue! ctx).getFirstUse! ctx = some opOperand then .operandNextUse opOperand' else if opOperand' = opOperand then .valueFirstUse ((opOperand'.getValue! ctx)) else opOperand.getBack! ctx) := by
  simp only [insertIntoCurrent]
  split <;> grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = (if opOperand' = opOperand then (opOperand'.getValue! ctx).getFirstUse! ctx else opOperand.getNextUse! ctx) := by
  simp only [insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getOperands! ctx := by
  simp only [OpOperandPtr.insertIntoCurrent]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumRegions! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getRegion! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.insertIntoCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.getValue! ctx) = (.blockArgument blockArg) then (opOperand' : Option OpOperandPtr) else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getLastBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = region.getLastBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getFirstBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getParent! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = region.getParent! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.getValue! ctx) = value then
      some opOperand'
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if opOperandPtr = .operandNextUse opOperand' then
      (opOperand'.getValue! ctx).getFirstUse! ctx
    else if opOperandPtr = .valueFirstUse ((opOperand'.getValue! ctx)) then
      some opOperand'
    else
      opOperandPtr.get! ctx := by
  grind

section BlockOperandPtr.removeFromCurrent

attribute [local grind] BlockOperandPtr.removeFromCurrent

@[grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = if (blockOperand'.getBack! ctx) = .blockFirstUse block then (blockOperand'.getNextUse! ctx) else block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getPrevBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getNextBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getParent! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getLastOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getPrevOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNextOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getParent! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getOpType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getAttributes! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getProperties! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumResults! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getIndex! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getOperands! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getOperands! ctx := by
  simp only [BlockOperandPtr.removeFromCurrent]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [removeFromCurrent]
  split <;> grind

@[grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [removeFromCurrent]
  split <;> grind

@[grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = (if (blockOperand'.getNextUse! ctx) = some blockOperand then (blockOperand'.getBack! ctx) else blockOperand.getBack! ctx) := by
  simp only [removeFromCurrent]
  split <;> grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = (if (blockOperand'.getBack! ctx) = .blockOperandNextUse blockOperand then (blockOperand'.getNextUse! ctx) else blockOperand.getNextUse! ctx) := by
  simp only [removeFromCurrent]
  split <;> grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumRegions! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getRegion! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_removeFromCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    if blockOperandPtr = (blockOperand'.getBack! ctx) then
      (blockOperand'.getNextUse! ctx)
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.removeFromCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getLastBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = region.getLastBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getFirstBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getParent! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = region.getParent! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_removeFromCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    opOperandPtr.get! ctx := by
  grind

end BlockOperandPtr.removeFromCurrent

section BlockOperandPtr.insertIntoCurrent

attribute [local grind] BlockOperandPtr.insertIntoCurrent

@[grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = if (blockOperand'.getValue! ctx) = block then some blockOperand' else block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getPrevBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getNextBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getParent! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getLastOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getPrevOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNextOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getParent! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getOpType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getAttributes! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getProperties! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumResults! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getIndex! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getOperands! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getOperands! ctx := by
  simp only [BlockOperandPtr.insertIntoCurrent]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [insertIntoCurrent]
  split <;> grind

@[grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [insertIntoCurrent]
  split <;> grind

@[grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = (if ((blockOperand'.getValue! ctx).getFirstUse! ctx) = some blockOperand then .blockOperandNextUse blockOperand' else if blockOperand' = blockOperand then .blockFirstUse ((blockOperand'.getValue! ctx)) else blockOperand.getBack! ctx) := by
  simp only [insertIntoCurrent]
  split <;> grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = (if blockOperand' = blockOperand then ((blockOperand'.getValue! ctx).getFirstUse! ctx) else blockOperand.getNextUse! ctx) := by
  simp only [insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumRegions! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getRegion! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_insertIntoCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    if blockOperandPtr = .blockOperandNextUse blockOperand' then
      ((blockOperand'.getValue! ctx).getFirstUse! ctx)
    else if blockOperandPtr = .blockFirstUse ((blockOperand'.getValue! ctx)) then
      some blockOperand'
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.insertIntoCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getLastBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = region.getLastBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getFirstBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getParent! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = region.getParent! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_insertIntoCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    opOperandPtr.get! ctx := by
  grind

end BlockOperandPtr.insertIntoCurrent

/- OperationPtr.linkBetween -/
section linkBetween
attribute [local grind] OperationPtr.linkBetween

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getLastOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getLastOp! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getFirstOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstOp! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getParent! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getParent! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getNextBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getNextBlock! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getPrevBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getPrevBlock! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstUse! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getPrevOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = if operation = next then some op' else if operation = op' then prev else operation.getPrevOp! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

set_option maxHeartbeats 1000000 in
@[grind =]
theorem OperationPtr.getNextOp!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNextOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = if operation = prev then some op' else if operation = op' then next else operation.getNextOp! ctx := by
  simp only [OperationPtr.linkBetween]
  grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getParent! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getParent! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.getOpType! (op'.linkBetween ctx prev next selfIn prevIn nextIn)) =
    (operation.getOpType! ctx) := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getAttributes! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getAttributes! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getProperties! (op'.linkBetween ctx prev next selfIn prevIn nextIn) opCode =
    operation.getProperties! ctx opCode := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumResults! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumResults! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getIndex! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumOperands! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumOperands! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getValue! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getBack! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getOperands! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getOperands! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumSuccessors! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumSuccessors! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumRegions! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumRegions! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getRegion! (op'.linkBetween ctx prev next selfIn prevIn nextIn) i =
    operation.getRegion! ctx i := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_linkBetween {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperandPtr.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getNumArguments! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    block.getNumArguments! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_linkBetween {region : RegionPtr} :
    region.getLastBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getLastBlock! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_linkBetween {region : RegionPtr} :
    region.getFirstBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getFirstBlock! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_linkBetween {region : RegionPtr} :
    region.getParent! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getParent! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_linkBetween {value : ValuePtr} :
    value.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getFirstUse! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_linkBetween {value : ValuePtr} :
    value.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getType! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_linkBetween {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperandPtr.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

end linkBetween

section setParentWithCheck

/- OperationPtr.setParentWithCheck -/
attribute [local grind] OperationPtr.setParentWithCheck

@[simp]
theorem BlockPtr.getLastOp!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  grind

grind_pattern BlockPtr.getLastOp!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getLastOp! newCtx

@[simp]
theorem BlockPtr.getFirstOp!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  grind

grind_pattern BlockPtr.getFirstOp!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getFirstOp! newCtx

@[simp]
theorem BlockPtr.getParent!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getParent! newCtx = block.getParent! ctx := by
  grind

grind_pattern BlockPtr.getParent!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getParent! newCtx

@[simp]
theorem BlockPtr.getNextBlock!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getNextBlock! newCtx = block.getNextBlock! ctx := by
  grind

grind_pattern BlockPtr.getNextBlock!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNextBlock! newCtx

@[simp]
theorem BlockPtr.getPrevBlock!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getPrevBlock! newCtx = block.getPrevBlock! ctx := by
  grind

grind_pattern BlockPtr.getPrevBlock!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getPrevBlock! newCtx

@[simp]
theorem BlockPtr.getFirstUse!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  grind

grind_pattern BlockPtr.getFirstUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getFirstUse! newCtx

@[simp]
theorem OperationPtr.getPrevOp!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  grind

grind_pattern OperationPtr.getPrevOp!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getPrevOp! newCtx)

@[simp]
theorem OperationPtr.getNextOp!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  simp only [OperationPtr.setParentWithCheck]
  grind

grind_pattern OperationPtr.getNextOp!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getNextOp! newCtx)

@[grind →]
theorem OperationPtr.getParent!_of_OperationPtr_setParentWithCheck_eq :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → op'.getParent! ctx = none := by
  grind

theorem OperationPtr.getParent!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getParent! newCtx = if operation = op' then some newParent else operation.getParent! ctx := by
  grind

grind_pattern OperationPtr.getParent!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getParent! newCtx)

@[simp]
theorem OperationPtr.getOpType!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  grind

grind_pattern OperationPtr.getOpType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getOpType! newCtx)

@[simp]
theorem OperationPtr.getAttributes!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  grind

grind_pattern OperationPtr.getAttributes!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getAttributes! newCtx)

@[simp]
theorem OperationPtr.getProperties!_OperationPtr_setParentWithCheck {operation : OperationPtr}
    (heq : op'.setParentWithCheck ctx newParent selfIn = some newCtx) :
    operation.getProperties! newCtx opCode =
    operation.getProperties! ctx opCode := by
  grind

grind_pattern OperationPtr.getProperties!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getProperties! newCtx opCode

@[simp]
theorem OperationPtr.getNumResults!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.getOwner!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

grind_pattern OpResultPtr.getOwner!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getOwner! newCtx

@[simp]
theorem OpResultPtr.getIndex!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getIndex! newCtx = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

grind_pattern OpResultPtr.getIndex!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getIndex! newCtx

@[simp]
theorem OpResultPtr.getFirstUse!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

grind_pattern OpResultPtr.getFirstUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getFirstUse! newCtx

@[simp]
theorem OpResultPtr.getType!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

grind_pattern OpResultPtr.getType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getType! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.getValue!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem OpOperandPtr.getOwner!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem OpOperandPtr.getBack!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem OpOperandPtr.getNextUse!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getOperands!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [OperationPtr.setParentWithCheck]
  grind

grind_pattern OperationPtr.getOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getOperands! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.getValue!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem BlockOperandPtr.getOwner!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem BlockOperandPtr.getBack!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_OperationPtr_setParentWithCheck {operandPtr : BlockOperandPtrPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getOwner! newCtx

@[simp]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getIndex! newCtx

@[simp]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getFirstUse! newCtx

@[simp]
theorem BlockArgumentPtr.getType!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getType! newCtx

@[simp]
theorem RegionPtr.getLastBlock!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getLastBlock! newCtx = region.getLastBlock! ctx := by
  grind

grind_pattern RegionPtr.getLastBlock!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, region.getLastBlock! newCtx

@[simp]
theorem RegionPtr.getFirstBlock!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getFirstBlock! newCtx = region.getFirstBlock! ctx := by
  grind

grind_pattern RegionPtr.getFirstBlock!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, region.getFirstBlock! newCtx

@[simp]
theorem RegionPtr.getParent!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  grind

grind_pattern RegionPtr.getParent!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, region.getParent! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_OperationPtr_setParentWithCheck {value : ValuePtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getFirstUse! newCtx

@[simp] -- No grind because of Unit
theorem ValuePtr.getType!_OperationPtr_setParentWithCheck {value : ValuePtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_OperationPtr_setParentWithCheck {opOperandPtr : OpOperandPtrPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opOperandPtr.get! newCtx

end setParentWithCheck

section linkBetweenWithParent

/- OperationPtr.linkBetweenWithParent -/
attribute [local grind] OperationPtr.linkBetweenWithParent

@[simp]
theorem BlockPtr.getFirstUse!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  grind

grind_pattern BlockPtr.getFirstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getFirstUse! newCtx)

@[simp]
theorem BlockPtr.getPrevBlock!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getPrevBlock! newCtx = block.getPrevBlock! ctx := by
  grind

grind_pattern BlockPtr.getPrevBlock!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getPrevBlock! newCtx)

@[simp]
theorem BlockPtr.getNextBlock!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getNextBlock! newCtx = block.getNextBlock! ctx := by
  grind

grind_pattern BlockPtr.getNextBlock!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getNextBlock! newCtx)

@[grind →]
theorem OperationPtr.getParent!_of_OperationPtr_linkBetweenWithParent_eq :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → op'.getParent! ctx = none := by
  grind

@[simp]
theorem BlockPtr.getParent!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getParent! newCtx = block.getParent! ctx := by
  grind

grind_pattern BlockPtr.getParent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getParent! newCtx)

theorem BlockPtr.getFirstOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstOp! newCtx = if parent = block ∧ prev = none then some op' else block.getFirstOp! ctx := by
  grind

grind_pattern BlockPtr.getFirstOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getFirstOp! newCtx)

theorem BlockPtr.getLastOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getLastOp! newCtx = if parent = block ∧ next = none then some op' else block.getLastOp! ctx := by
  grind

grind_pattern BlockPtr.getLastOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getLastOp! newCtx)

theorem OperationPtr.getPrevOp!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getPrevOp! newCtx = if operation = next then some op' else if operation = op' then prev else operation.getPrevOp! ctx := by
  grind

grind_pattern OperationPtr.getPrevOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getPrevOp! newCtx)

theorem OperationPtr.getNextOp!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getNextOp! newCtx = if operation = prev then some op' else if operation = op' then next else operation.getNextOp! ctx := by
  grind

grind_pattern OperationPtr.getNextOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getNextOp! newCtx)

theorem OperationPtr.getParent!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getParent! newCtx = if operation = op' then some parent else operation.getParent! ctx := by
  grind

grind_pattern OperationPtr.getParent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getParent! newCtx)

@[simp]
theorem OperationPtr.getOpType!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.getOpType! newCtx) = (operation.getOpType! ctx) := by
  grind

grind_pattern OperationPtr.getOpType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getOpType! newCtx)

@[simp]
theorem OperationPtr.getAttributes!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  grind

grind_pattern OperationPtr.getAttributes!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getAttributes! newCtx)

@[simp]
theorem OperationPtr.getProperties!_OperationPtr_linkBetweenWithParent {operation : OperationPtr}
    (heq : op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx) :
    operation.getProperties! newCtx opCode =
    operation.getProperties! ctx opCode := by
  grind

grind_pattern OperationPtr.getProperties!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getProperties! newCtx opCode

@[simp]
theorem OperationPtr.getNumResults!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.getOwner!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

grind_pattern OpResultPtr.getOwner!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getOwner! newCtx

@[simp]
theorem OpResultPtr.getIndex!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getIndex! newCtx = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

grind_pattern OpResultPtr.getIndex!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getIndex! newCtx

@[simp]
theorem OpResultPtr.getFirstUse!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

grind_pattern OpResultPtr.getFirstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getFirstUse! newCtx

@[simp]
theorem OpResultPtr.getType!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

grind_pattern OpResultPtr.getType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getType! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.getValue!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem OpOperandPtr.getOwner!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem OpOperandPtr.getBack!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem OpOperandPtr.getNextUse!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getOperands!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [OperationPtr.linkBetweenWithParent]
  grind

grind_pattern OperationPtr.getOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getOperands! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.getValue!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem BlockOperandPtr.getOwner!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem BlockOperandPtr.getBack!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem BlockOperandPtr.getNextUse!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent {operandPtr : BlockOperandPtrPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.getOwner!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getOwner! newCtx

@[simp]
theorem BlockArgumentPtr.getIndex!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getIndex! newCtx

@[simp]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getFirstUse! newCtx

@[simp]
theorem BlockArgumentPtr.getType!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getType! newCtx

@[simp]
theorem RegionPtr.getLastBlock!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getLastBlock! newCtx = region.getLastBlock! ctx := by
  grind

grind_pattern RegionPtr.getLastBlock!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.getLastBlock! newCtx

@[simp]
theorem RegionPtr.getFirstBlock!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getFirstBlock! newCtx = region.getFirstBlock! ctx := by
  grind

grind_pattern RegionPtr.getFirstBlock!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.getFirstBlock! newCtx

@[simp]
theorem RegionPtr.getParent!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  grind

grind_pattern RegionPtr.getParent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.getParent! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_OperationPtr_linkBetweenWithParent {value : ValuePtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getFirstUse! newCtx

theorem ValuePtr.getType!_OperationPtr_linkBetweenWithParent {value : ValuePtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent {opOperandPtr : OpOperandPtrPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opOperandPtr.get! newCtx

end linkBetweenWithParent

/- BlockPtr.linkBetween -/
section linkBetween

unseal BlockPtr.linkBetween
attribute [local grind] BlockPtr.linkBetween

--  -   * Block.firstUse
--  -   * Block.prev
--  -   * Block.next
--  -   * Block.parent
--  -   * Block.firstOp
--  -   * Block.lastOp

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstUse! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getPrevBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = if block = next then some block' else if block = block' then prev else block.getPrevBlock! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getNextBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = if block = prev then some block' else if block = block' then next else block.getNextBlock! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getParent! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getParent! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getFirstOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstOp! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getLastOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getLastOp! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getRegions! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getRegions! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getAttributes! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getAttributes! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getParent! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getParent! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getPrevOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getPrevOp! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNextOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getNextOp! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getOpType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getOpType! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumResults! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getNumResults! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getIndex! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumOperands! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumOperands! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getValue! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getBack! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getNextUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getOperands! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getOperands! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumSuccessors! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumSuccessors! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumRegions! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumRegions! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getRegion! (block'.linkBetween ctx prev next selfIn prevIn nextIn) i =
    operation.getRegion! ctx i := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_linkBetween {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperandPtr.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getNumArguments! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    block.getNumArguments! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_linkBetween {region : RegionPtr} :
    region.getLastBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getLastBlock! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_linkBetween {region : RegionPtr} :
    region.getFirstBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getFirstBlock! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_linkBetween {region : RegionPtr} :
    region.getParent! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getParent! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_linkBetween {value : ValuePtr} :
    value.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getFirstUse! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_linkBetween {value : ValuePtr} :
    value.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    value.getType! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperandPtr.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

end linkBetween

section setParentWithCheck

/- OperationPtr.setParentWithCheck -/
unseal BlockPtr.setParentWithCheck
attribute [local grind] BlockPtr.setParentWithCheck

@[grind →]
theorem BlockPtr.getParent!_of_BlockPtr_setParentWithCheck_eq :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block'.getParent! ctx = none := by
  grind

theorem BlockPtr.getFirstUse!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  grind

grind_pattern BlockPtr.getFirstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.getFirstUse! newCtx)

theorem BlockPtr.getPrevBlock!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getPrevBlock! newCtx = block.getPrevBlock! ctx := by
  grind

grind_pattern BlockPtr.getPrevBlock!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.getPrevBlock! newCtx)

theorem BlockPtr.getNextBlock!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getNextBlock! newCtx = block.getNextBlock! ctx := by
  grind

grind_pattern BlockPtr.getNextBlock!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.getNextBlock! newCtx)

theorem BlockPtr.getParent!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getParent! newCtx = if block = block' then some newParent else block.getParent! ctx := by
  grind

grind_pattern BlockPtr.getParent!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.getParent! newCtx)

theorem BlockPtr.getFirstOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  grind

grind_pattern BlockPtr.getFirstOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.getFirstOp! newCtx)

theorem BlockPtr.getLastOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  grind

grind_pattern BlockPtr.getLastOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.getLastOp! newCtx)

@[simp]
theorem OperationPtr.getRegions!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getRegions! newCtx = operation.getRegions! ctx := by
  grind

grind_pattern OperationPtr.getRegions!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegions! newCtx

@[simp]
theorem OperationPtr.getAttributes!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  grind

grind_pattern OperationPtr.getAttributes!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getAttributes! newCtx

@[simp]
theorem OperationPtr.getParent!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getParent! newCtx = operation.getParent! ctx := by
  grind

grind_pattern OperationPtr.getParent!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getParent! newCtx

@[simp]
theorem OperationPtr.getPrevOp!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  grind

grind_pattern OperationPtr.getPrevOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getPrevOp! newCtx

@[simp]
theorem OperationPtr.getNextOp!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  grind

grind_pattern OperationPtr.getNextOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNextOp! newCtx

@[simp]
theorem OperationPtr.getOpType!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  grind

grind_pattern OperationPtr.getOpType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getOpType! newCtx

@[simp]
theorem OperationPtr.getNumResults!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.getOwner!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

grind_pattern OpResultPtr.getOwner!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getOwner! newCtx

@[simp]
theorem OpResultPtr.getIndex!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getIndex! newCtx = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

grind_pattern OpResultPtr.getIndex!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getIndex! newCtx

@[simp]
theorem OpResultPtr.getFirstUse!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

grind_pattern OpResultPtr.getFirstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getFirstUse! newCtx

@[simp]
theorem OpResultPtr.getType!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

grind_pattern OpResultPtr.getType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.getType! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.getValue!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem OpOperandPtr.getOwner!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem OpOperandPtr.getBack!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem OpOperandPtr.getNextUse!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getOperands!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [BlockPtr.setParentWithCheck]
  grind

grind_pattern OperationPtr.getOperands!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getOperands! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.getValue!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem BlockOperandPtr.getOwner!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem BlockOperandPtr.getBack!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_BlockPtr_setParentWithCheck {operandPtr : BlockOperandPtrPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getOwner! newCtx

@[simp]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getIndex! newCtx

@[simp]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getFirstUse! newCtx

@[simp]
theorem BlockArgumentPtr.getType!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.getType! newCtx

@[simp]
theorem RegionPtr.getLastBlock!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getLastBlock! newCtx = region.getLastBlock! ctx := by
  grind

grind_pattern RegionPtr.getLastBlock!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, region.getLastBlock! newCtx

@[simp]
theorem RegionPtr.getFirstBlock!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getFirstBlock! newCtx = region.getFirstBlock! ctx := by
  grind

grind_pattern RegionPtr.getFirstBlock!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, region.getFirstBlock! newCtx

@[simp]
theorem RegionPtr.getParent!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  grind

grind_pattern RegionPtr.getParent!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, region.getParent! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_BlockPtr_setParentWithCheck {value : ValuePtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getFirstUse! newCtx

@[simp] -- No grind because of Unit
theorem ValuePtr.getType!_BlockPtr_setParentWithCheck {value : ValuePtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_BlockPtr_setParentWithCheck {opOperandPtr : OpOperandPtrPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opOperandPtr.get! newCtx

end setParentWithCheck

section linkBetweenWithParent

/- OperationPtr.linkBetweenWithParent -/
unseal BlockPtr.linkBetweenWithParent
attribute [local grind] BlockPtr.linkBetweenWithParent

@[grind →]
theorem BlockPtr.getParent!_of_BlockPtr_linkBetweenWithParent_eq :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block'.getParent! ctx = none := by
  grind

@[simp]
theorem BlockPtr.getFirstUse!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  grind

grind_pattern BlockPtr.getFirstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getFirstUse! newCtx)

theorem BlockPtr.getPrevBlock!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getPrevBlock! newCtx = if block = next then some block' else if block = block' then prev else block.getPrevBlock! ctx := by
  grind

grind_pattern BlockPtr.getPrevBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getPrevBlock! newCtx)

@[simp]
theorem BlockPtr.getNextBlock!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getNextBlock! newCtx = if block = prev then some block' else if block = block' then next else block.getNextBlock! ctx := by
  grind

grind_pattern BlockPtr.getNextBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getNextBlock! newCtx)

@[simp]
theorem BlockPtr.getParent!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getParent! newCtx = if block = block' then some parent else block.getParent! ctx := by
  grind

grind_pattern BlockPtr.getParent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getParent! newCtx)

theorem BlockPtr.getFirstOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  grind

grind_pattern BlockPtr.getFirstOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getFirstOp! newCtx)

theorem BlockPtr.getLastOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  grind

grind_pattern BlockPtr.getLastOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.getLastOp! newCtx)

theorem OperationPtr.getRegions!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getRegions! newCtx = operation.getRegions! ctx := by
  grind

grind_pattern OperationPtr.getRegions!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegions! newCtx

theorem OperationPtr.getAttributes!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  grind

grind_pattern OperationPtr.getAttributes!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getAttributes! newCtx

theorem OperationPtr.getParent!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getParent! newCtx = operation.getParent! ctx := by
  grind

grind_pattern OperationPtr.getParent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getParent! newCtx

theorem OperationPtr.getPrevOp!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  grind

grind_pattern OperationPtr.getPrevOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getPrevOp! newCtx

theorem OperationPtr.getNextOp!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  grind

grind_pattern OperationPtr.getNextOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNextOp! newCtx

theorem OperationPtr.getOpType!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  grind

grind_pattern OperationPtr.getOpType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getOpType! newCtx

@[simp]
theorem OperationPtr.getNumResults!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumResults! newCtx = operation.getNumResults! ctx := by
  grind

grind_pattern OperationPtr.getNumResults!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumResults! newCtx

@[simp]
theorem OpResultPtr.getOwner!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  unfold BlockPtr.linkBetweenWithParent
  grind

grind_pattern OpResultPtr.getOwner!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getOwner! newCtx

@[simp]
theorem OpResultPtr.getIndex!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getIndex! newCtx = opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  unfold BlockPtr.linkBetweenWithParent
  grind

grind_pattern OpResultPtr.getIndex!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getIndex! newCtx

@[simp]
theorem OpResultPtr.getFirstUse!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  unfold BlockPtr.linkBetweenWithParent
  grind

grind_pattern OpResultPtr.getFirstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getFirstUse! newCtx

@[simp]
theorem OpResultPtr.getType!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  unfold BlockPtr.linkBetweenWithParent
  grind

grind_pattern OpResultPtr.getType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.getType! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.getValue!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

grind_pattern OpOperandPtr.getValue!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem OpOperandPtr.getOwner!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

grind_pattern OpOperandPtr.getOwner!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem OpOperandPtr.getBack!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

grind_pattern OpOperandPtr.getBack!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem OpOperandPtr.getNextUse!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

grind_pattern OpOperandPtr.getNextUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getOperands!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getOperands! newCtx = operation.getOperands! ctx := by
  simp only [BlockPtr.linkBetweenWithParent]
  grind

grind_pattern OperationPtr.getOperands!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getOperands! newCtx

@[simp]
theorem OperationPtr.getNumSuccessors!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumSuccessors! newCtx = operation.getNumSuccessors! ctx := by
  grind

grind_pattern OperationPtr.getNumSuccessors!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumSuccessors! newCtx

@[simp]
theorem BlockOperandPtr.getValue!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

grind_pattern BlockOperandPtr.getValue!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getValue! newCtx

@[simp]
theorem BlockOperandPtr.getOwner!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

grind_pattern BlockOperandPtr.getOwner!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getOwner! newCtx

@[simp]
theorem BlockOperandPtr.getBack!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

grind_pattern BlockOperandPtr.getBack!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getBack! newCtx

@[simp]
theorem BlockOperandPtr.getNextUse!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

grind_pattern BlockOperandPtr.getNextUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.getNextUse! newCtx

@[simp]
theorem OperationPtr.getNumRegions!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumRegions! newCtx = operation.getNumRegions! ctx := by
  grind

grind_pattern OperationPtr.getNumRegions!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumRegions! newCtx

@[simp]
theorem OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getRegion! newCtx i = operation.getRegion! ctx i := by
  grind

grind_pattern OperationPtr.getRegion!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getRegion! newCtx i

@[simp]
theorem BlockOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent {operandPtr : BlockOperandPtrPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operandPtr.get! newCtx = operandPtr.get! ctx := by
  grind

grind_pattern BlockOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operandPtr.get! newCtx

@[simp]
theorem BlockPtr.getNumArguments!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    block.getNumArguments! newCtx = block.getNumArguments! ctx := by
  grind

grind_pattern BlockPtr.getNumArguments!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, block.getNumArguments! newCtx

@[simp]
theorem BlockArgumentPtr.getOwner!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

grind_pattern BlockArgumentPtr.getOwner!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getOwner! newCtx

@[simp]
theorem BlockArgumentPtr.getIndex!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

grind_pattern BlockArgumentPtr.getIndex!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getIndex! newCtx

@[simp]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

grind_pattern BlockArgumentPtr.getFirstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getFirstUse! newCtx

@[simp]
theorem BlockArgumentPtr.getType!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

grind_pattern BlockArgumentPtr.getType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.getType! newCtx

@[simp]
theorem RegionPtr.getFirstBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getFirstBlock! newCtx = if prev = none ∧ region = parent then some block' else region.getFirstBlock! ctx := by
  grind [RegionPtr.getFirstBlock!_BlockPtr_setParentWithCheck]

grind_pattern RegionPtr.getFirstBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.getFirstBlock! newCtx

@[simp]
theorem RegionPtr.getLastBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getLastBlock! newCtx = if next = none ∧ region = parent then some block' else region.getLastBlock! ctx := by
  grind [RegionPtr.getLastBlock!_BlockPtr_setParentWithCheck]

grind_pattern RegionPtr.getLastBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.getLastBlock! newCtx

@[simp]
theorem RegionPtr.getParent!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  grind [RegionPtr.getParent!_BlockPtr_setParentWithCheck]

grind_pattern RegionPtr.getParent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.getParent! newCtx

@[simp]
theorem ValuePtr.getFirstUse!_BlockPtr_linkBetweenWithParent {value : ValuePtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getFirstUse! newCtx = value.getFirstUse! ctx := by
  grind

grind_pattern ValuePtr.getFirstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getFirstUse! newCtx

theorem ValuePtr.getType!_BlockPtr_linkBetweenWithParent {value : ValuePtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    value.getType! newCtx = value.getType! ctx := by
  grind

grind_pattern ValuePtr.getType!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, value.getType! newCtx

@[simp]
theorem OpOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent {opOperandPtr : OpOperandPtrPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opOperandPtr.get! newCtx = opOperandPtr.get! ctx := by
  grind

grind_pattern OpOperandPtrPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opOperandPtr.get! newCtx

end linkBetweenWithParent
