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
theorem BlockPtr.firstUse!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getPrevBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getNextBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getParent! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getLastOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getPrevOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNextOp! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getParent! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.getOpType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)) =
    (operation.getOpType! ctx) := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getAttributes! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_OpOperandPtr_removeFromCurrent
  | grind

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
theorem OpResultPtr.get!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse (.opResult opResult) then
      { opResult.get! ctx with firstUse := (opOperand'.get! ctx).nextUse }
    else
      opResult.get! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.get! ctx).back = .valueFirstUse (.opResult opResult) then ((opOperand'.get! ctx).nextUse) else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem OpResultPtr.getType!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    { opOperand.get! ctx with
        back :=
          if (opOperand'.get! ctx).nextUse = some opOperand then
            (opOperand'.get! ctx).back
          else
            (opOperand.get! ctx).back
        nextUse :=
          if (opOperand'.get! ctx).back = .operandNextUse opOperand then
            (opOperand'.get! ctx).nextUse
          else
            (opOperand.get! ctx).nextUse
    } := by
  simp [removeFromCurrent]
  split
  · split
    · grind
    · split
      · grind
      · -- TODO: Why doesn't 'grind' work here?
        simp only [get!_OpOperandPtrPtr_set, ite_eq_right_iff]
        grind
  · split
    · grind
    · split
      · grind
      · simp [OpOperandPtr.get!_OpOperandPtr_setBack]
        split
        · grind
        · simp only [get!_OpOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = (if (opOperand'.get! ctx).nextUse = some opOperand then (opOperand'.get! ctx).back else opOperand.getBack! ctx) := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = (if (opOperand'.get! ctx).back = .operandNextUse opOperand then (opOperand'.get! ctx).nextUse else opOperand.getNextUse! ctx) := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

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
theorem BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

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
theorem BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse (.blockArgument blockArg) then
      { blockArg.get! ctx with firstUse := (opOperand'.get! ctx).nextUse }
    else
      blockArg.get! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.get! ctx).back = .valueFirstUse (.blockArgument blockArg) then ((opOperand'.get! ctx).nextUse) else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getLastBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getFirstBlock! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getParent! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_OpOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse value then
      (opOperand'.get! ctx).nextUse
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
    if opOperandPtr = (opOperand'.get! ctx).back then
      (opOperand'.get! ctx).nextUse
    else
      opOperandPtr.get! ctx := by
  grind

/- OpOperandPtr.insertIntoCurrent -/
attribute [local grind] OpOperandPtr.insertIntoCurrent

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getPrevBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getNextBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getParent! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getLastOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getPrevOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNextOp! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getParent! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getOpType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getAttributes! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_OpOperandPtr_insertIntoCurrent
  | grind

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
theorem OpResultPtr.get!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = (.opResult opResult) then
      { opResult.get! ctx with firstUse := opOperand' }
    else
      opResult.get! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.get! ctx).value = (.opResult opResult) then (opOperand' : Option OpOperandPtr) else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem OpResultPtr.getType!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    { opOperand.get! ctx with
        back :=
          if (opOperand'.get! ctx).value.getFirstUse! ctx = some opOperand then
            .operandNextUse opOperand'
          else if opOperand' = opOperand then
            .valueFirstUse ((opOperand'.get! ctx).value)
          else
            (opOperand.get! ctx).back
        nextUse :=
          if opOperand' = opOperand then
            (opOperand'.get! ctx).value.getFirstUse! ctx
          else
            (opOperand.get! ctx).nextUse
    } := by
  simp only [insertIntoCurrent]
  by_cases h: opOperand = opOperand'
  · grind
  · simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack]
    split
    · rename_i h₁
      simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack] at h₁
      simp only [get!_ValuePtr_setFirstUse]
      simp only [OpOperandPtr.get!_OpOperandPtr_setNextUse, h, ↓reduceIte]
      simp only [get!_OpOperandPtr_setBack, h, ↓reduceIte]
      simp only [Ne.symm h, ↓reduceIte]
      simp only [h₁, reduceCtorEq, ↓reduceIte]
    · rename_i ptr h₁
      simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack] at h₁
      simp [h₁]
      by_cases heq: ptr = opOperand
      · grind
      · simp only [Ne.symm h, ↓reduceIte, heq]
        simp only [get!_OpOperandPtr_setBack, Ne.symm heq, ↓reduceIte, get!_ValuePtr_setFirstUse]
        simp only [get!_OpOperandPtr_setNextUse, h, ↓reduceIte]
        simp only [get!_OpOperandPtr_setBack]
        --grind    -- Why does 'grind' not work here?
        simp only [h, ↓reduceIte]

@[grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = (if (opOperand'.get! ctx).value.getFirstUse! ctx = some opOperand then .operandNextUse opOperand' else if opOperand' = opOperand then .valueFirstUse ((opOperand'.get! ctx).value) else opOperand.getBack! ctx) := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = (if opOperand' = opOperand then (opOperand'.get! ctx).value.getFirstUse! ctx else opOperand.getNextUse! ctx) := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

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
theorem BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

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
theorem BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = (.blockArgument blockArg) then
      { blockArg.get! ctx with firstUse := opOperand' }
    else
      blockArg.get! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = if (opOperand'.get! ctx).value = (.blockArgument blockArg) then (opOperand' : Option OpOperandPtr) else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getLastBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getFirstBlock! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getParent! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_OpOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = value then
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
      (opOperand'.get! ctx).value.getFirstUse! ctx
    else if opOperandPtr = .valueFirstUse ((opOperand'.get! ctx).value) then
      some opOperand'
    else
      opOperandPtr.get! ctx := by
  grind

section BlockOperandPtr.removeFromCurrent

attribute [local grind] BlockOperandPtr.removeFromCurrent

@[grind =]
theorem BlockPtr.firstUse!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).firstUse =
    if (blockOperand'.get! ctx).back = .blockFirstUse block then
      (blockOperand'.get! ctx).nextUse
    else
      (block.get! ctx).firstUse := by
  grind

@[grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = if (blockOperand'.get! ctx).back = .blockFirstUse block then (blockOperand'.get! ctx).nextUse else block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getPrevBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getNextBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getParent! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getFirstOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} :
    block.getLastOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getPrevOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNextOp! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getParent! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getOpType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getAttributes! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_BlockOperandPtr_removeFromCurrent
  | grind

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
theorem OpResultPtr.get!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

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
theorem BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) =
    { blockOperand.get! ctx with
        back :=
          if (blockOperand'.get! ctx).nextUse = some blockOperand then
            (blockOperand'.get! ctx).back
          else
            (blockOperand.get! ctx).back
        nextUse :=
          if (blockOperand'.get! ctx).back = .blockOperandNextUse blockOperand then
            (blockOperand'.get! ctx).nextUse
          else
            (blockOperand.get! ctx).nextUse
    } := by
  simp [removeFromCurrent]
  split
  · split
    · grind
    · split
      · grind
      · -- TODO: Why doesn't 'grind' work here?
        simp only [get!_BlockOperandPtrPtr_set, ite_eq_right_iff]
        grind
  · split
    · grind
    · split
      · grind
      · simp only [get!_BlockOperandPtr_setBack]
        split
        · grind
        · simp only [get!_BlockOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = (if (blockOperand'.get! ctx).nextUse = some blockOperand then (blockOperand'.get! ctx).back else blockOperand.getBack! ctx) := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (blockOperand'.removeFromCurrent ctx hblockOperand' ctxInBounds) = (if (blockOperand'.get! ctx).back = .blockOperandNextUse blockOperand then (blockOperand'.get! ctx).nextUse else blockOperand.getNextUse! ctx) := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

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
    if blockOperandPtr = (blockOperand'.get! ctx).back then
      (blockOperand'.get! ctx).nextUse
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_removeFromCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (blockOperand'.removeFromCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.get! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getLastBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getFirstBlock! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.getParent! (blockOperand'.removeFromCurrent ctx hOperand' ctxInBounds) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_BlockOperandPtr_removeFromCurrent
  | grind

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
theorem BlockPtr.firstUse!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).firstUse =
    if (blockOperand'.get! ctx).value = block then
      some blockOperand'
    else
      (block.get! ctx).firstUse := by
  grind

@[grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = if (blockOperand'.get! ctx).value = block then some blockOperand' else block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getPrevBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getNextBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getParent! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getFirstOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_insertIntoCurrent {block : BlockPtr} :
    block.getLastOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getPrevOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNextOp! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getParent! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getOpType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getAttributes! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_BlockOperandPtr_insertIntoCurrent
  | grind

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
theorem OpResultPtr.get!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getValue! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getBack! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

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
theorem BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    { blockOperand.get! ctx with
        back :=
          if ((blockOperand'.get! ctx).value.get! ctx).firstUse = some blockOperand then
            .blockOperandNextUse blockOperand'
          else if blockOperand' = blockOperand then
            .blockFirstUse ((blockOperand'.get! ctx).value)
          else
            (blockOperand.get! ctx).back
        nextUse :=
          if blockOperand' = blockOperand then
            ((blockOperand'.get! ctx).value.get! ctx).firstUse
          else
            (blockOperand.get! ctx).nextUse
    } := by
  simp only [insertIntoCurrent]
  by_cases h: blockOperand = blockOperand'
  · grind
  · simp only [← get!_eq_get, ← BlockPtr.get!_eq_get, BlockPtr.get!_BlockOperandPtr_setBack]
    split
    · rename_i h₁
      simp only [← get!_eq_get, ← BlockPtr.get!_eq_get, BlockPtr.get!_BlockOperandPtr_setBack] at h₁
      simp only [get!_BlockPtr_setFirstUse, get!_BlockOperandPtr_setNextUse, h, ↓reduceIte,
        get!_BlockOperandPtr_setBack]
      simp only [Ne.symm h, ↓reduceIte]
      simp only [h₁, reduceCtorEq, ↓reduceIte]
    · rename_i ptr h₁
      simp only [← get!_eq_get, ← BlockPtr.get!_eq_get, BlockPtr.get!_BlockOperandPtr_setBack] at h₁
      simp [h₁]
      by_cases heq: ptr = blockOperand
      · grind
      · simp only [Ne.symm h, ↓reduceIte, heq]
        simp only [get!_BlockOperandPtr_setBack, Ne.symm heq, ↓reduceIte, get!_BlockPtr_setFirstUse]
        simp only [get!_BlockOperandPtr_setNextUse, h, ↓reduceIte]
        simp only [get!_BlockOperandPtr_setBack]
        --grind    -- Why does 'grind' not work here?
        simp only [h, ↓reduceIte]

@[grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = (if ((blockOperand'.get! ctx).value.get! ctx).firstUse = some blockOperand then .blockOperandNextUse blockOperand' else if blockOperand' = blockOperand then .blockFirstUse ((blockOperand'.get! ctx).value) else blockOperand.getBack! ctx) := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = (if blockOperand' = blockOperand then ((blockOperand'.get! ctx).value.get! ctx).firstUse else blockOperand.getNextUse! ctx) := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

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
      ((blockOperand'.get! ctx).value.get! ctx).firstUse
    else if blockOperandPtr = .blockFirstUse ((blockOperand'.get! ctx).value) then
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
theorem BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.get! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getLastBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getFirstBlock! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.getParent! (blockOperand'.insertIntoCurrent ctx hblockOperand' ctxInBounds) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_BlockOperandPtr_insertIntoCurrent
  | grind

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
theorem BlockPtr.get!_OperationPtr_linkBetween {block : BlockPtr} :
    block.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    block.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getLastOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getFirstOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getParent! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getNextBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getPrevBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_linkBetween {block : BlockPtr} :
    block.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.get!_OperationPtr_linkBetween
  | grind

@[grind =]
theorem OperationPtr.prev!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).prev =
    if operation = next then
      some op'
    else if operation = op' then
      prev
    else
      (operation.get! ctx).prev := by
  simp only [OperationPtr.linkBetween]
  grind

@[grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getPrevOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = if operation = next then some op' else if operation = op' then prev else operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_OperationPtr_linkBetween
  | grind

set_option maxHeartbeats 1000000 in
@[grind =]
theorem OperationPtr.next!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).next =
    if operation = prev then
      some op'
    else if operation = op' then
      next
    else
      (operation.get! ctx).next := by
  simp only [OperationPtr.linkBetween]
  grind (gen := 20)

@[grind =]
theorem OperationPtr.getNextOp!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNextOp! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = if operation = prev then some op' else if operation = op' then next else operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).parent =
    (operation.get! ctx).parent := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getParent! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.getOpType! (op'.linkBetween ctx prev next selfIn prevIn nextIn)) =
    (operation.getOpType! ctx) := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_linkBetween {operation : OperationPtr} :
    (operation.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn)).attrs =
    (operation.get! ctx).attrs := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getAttributes! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_OperationPtr_linkBetween
  | grind

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
theorem OpResultPtr.get!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opResult.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetween {operation : OperationPtr} :
    operation.getNumOperands! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumOperands! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperand.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getValue! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getBack! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_linkBetween {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetween
  | grind

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
theorem BlockOperandPtr.get!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperand.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetween
  | grind

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
theorem BlockArgumentPtr.get!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockArg.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getType! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_linkBetween {region : RegionPtr} :
    region.get! (op'.linkBetween ctx prev next selfIn prevIn nextIn) =
    region.get! ctx := by
  simp only [OperationPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_linkBetween {region : RegionPtr} :
    region.getLastBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_linkBetween {region : RegionPtr} :
    region.getFirstBlock! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_OperationPtr_linkBetween
  | grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_linkBetween {region : RegionPtr} :
    region.getParent! (op'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_OperationPtr_linkBetween
  | grind

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
theorem BlockPtr.get!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx) = (block.get! ctx) := by
  grind

@[simp]
theorem BlockPtr.getLastOp!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockPtr.getFirstOp!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockPtr.getParent!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getParent! newCtx = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockPtr.getNextBlock!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getNextBlock! newCtx = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockPtr.getPrevBlock!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getPrevBlock! newCtx = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockPtr.getFirstUse!_OperationPtr_setParentWithCheck {block : BlockPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockPtr.get!_OperationPtr_setParentWithCheck]

grind_pattern BlockPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, block.get! newCtx

@[simp]
theorem OperationPtr.prev!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).prev = (operation.get! ctx).prev := by
  grind

@[simp]
theorem OperationPtr.getPrevOp!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_OperationPtr_setParentWithCheck
  | grind [OperationPtr.prev!_OperationPtr_setParentWithCheck]

grind_pattern OperationPtr.prev!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).prev

@[simp]
theorem OperationPtr.next!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).next = (operation.get! ctx).next := by
  simp only [OperationPtr.setParentWithCheck]
  grind

@[simp]
theorem OperationPtr.getNextOp!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_OperationPtr_setParentWithCheck
  | grind [OperationPtr.next!_OperationPtr_setParentWithCheck]

grind_pattern OperationPtr.next!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).next

@[grind →]
theorem OperationPtr.parent!_of_OperationPtr_setParentWithCheck_eq :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (op'.get! ctx).parent = none := by
  grind

@[grind →]
theorem OperationPtr.getParent!_of_OperationPtr_setParentWithCheck_eq :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → op'.getParent! ctx = none := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_of_OperationPtr_setParentWithCheck_eq
  | grind

theorem OperationPtr.parent!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).parent =
    if operation = op' then
      some newParent
    else
      (operation.get! ctx).parent := by
  grind

theorem OperationPtr.getParent!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getParent! newCtx = if operation = op' then some newParent else operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_OperationPtr_setParentWithCheck
  | grind [OperationPtr.parent!_OperationPtr_setParentWithCheck]

grind_pattern OperationPtr.parent!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).parent

@[simp]
theorem OperationPtr.getOpType!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getOpType! newCtx = operation.getOpType! ctx := by
  grind

grind_pattern OperationPtr.getOpType!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.getOpType! newCtx)

@[simp]
theorem OperationPtr.attrs!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

@[simp]
theorem OperationPtr.getAttributes!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_OperationPtr_setParentWithCheck
  | grind [OperationPtr.attrs!_OperationPtr_setParentWithCheck]

grind_pattern OperationPtr.attrs!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, (operation.get! newCtx).attrs

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
theorem OpResultPtr.get!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  grind

@[simp]
theorem OpResultPtr.getOwner!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpResultPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem OpResultPtr.getFirstUse!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpResultPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem OpResultPtr.getType!_OperationPtr_setParentWithCheck {opResult : OpResultPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpResultPtr.get!_OperationPtr_setParentWithCheck]

grind_pattern OpResultPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck {operation : OperationPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem OpOperandPtr.getValue!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem OpOperandPtr.getOwner!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem OpOperandPtr.getBack!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem OpOperandPtr.getNextUse!_OperationPtr_setParentWithCheck {operand : OpOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_OperationPtr_setParentWithCheck]

grind_pattern OpOperandPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

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
theorem BlockOperandPtr.get!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem BlockOperandPtr.getValue!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockOperandPtr.getOwner!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockOperandPtr.getBack!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setParentWithCheck {operand : BlockOperandPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_OperationPtr_setParentWithCheck]

grind_pattern BlockOperandPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

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
theorem BlockArgumentPtr.get!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

@[simp]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem BlockArgumentPtr.getType!_OperationPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_OperationPtr_setParentWithCheck]

grind_pattern BlockArgumentPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx →
    region.get! newCtx = region.get! ctx := by
  grind

@[simp]
theorem RegionPtr.getLastBlock!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getLastBlock! newCtx = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_OperationPtr_setParentWithCheck
  | grind [RegionPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem RegionPtr.getFirstBlock!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getFirstBlock! newCtx = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_OperationPtr_setParentWithCheck
  | grind [RegionPtr.get!_OperationPtr_setParentWithCheck]

@[simp]
theorem RegionPtr.getParent!_OperationPtr_setParentWithCheck {region : RegionPtr} :
    op'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_OperationPtr_setParentWithCheck
  | grind [RegionPtr.get!_OperationPtr_setParentWithCheck]

grind_pattern RegionPtr.get!_OperationPtr_setParentWithCheck =>
  op'.setParentWithCheck ctx newParent selfIn, some newCtx, region.get! newCtx

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
theorem BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse
    := by
  grind

@[simp]
theorem BlockPtr.getFirstUse!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent
  | grind [BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockPtr.firstUse!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstUse

@[simp]
theorem BlockPtr.prev!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev
    := by
  grind

@[simp]
theorem BlockPtr.getPrevBlock!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getPrevBlock! newCtx = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_OperationPtr_linkBetweenWithParent
  | grind [BlockPtr.prev!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockPtr.prev!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).prev

@[simp]
theorem BlockPtr.next!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next
    := by
  grind

@[simp]
theorem BlockPtr.getNextBlock!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getNextBlock! newCtx = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_OperationPtr_linkBetweenWithParent
  | grind [BlockPtr.next!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockPtr.next!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).next

@[grind →]
theorem OperationPtr.parent!_of_OperationPtr_linkBetweenWithParent_eq :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (op'.get! ctx).parent = none := by
  grind

@[grind →]
theorem OperationPtr.getParent!_of_OperationPtr_linkBetweenWithParent_eq :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → op'.getParent! ctx = none := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_of_OperationPtr_linkBetweenWithParent_eq
  | grind

@[simp]
theorem BlockPtr.parent!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).parent = (block.get! ctx).parent := by
  grind

@[simp]
theorem BlockPtr.getParent!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getParent! newCtx = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_OperationPtr_linkBetweenWithParent
  | grind [BlockPtr.parent!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockPtr.parent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstOp =
    if parent = block ∧ prev = none then
      some op'
    else
      (block.get! ctx).firstOp := by
  grind

theorem BlockPtr.getFirstOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstOp! newCtx = if parent = block ∧ prev = none then some op' else block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent
  | grind [BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockPtr.firstOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).lastOp =
    if parent = block ∧ next = none then
      some op'
    else
      (block.get! ctx).lastOp := by
  grind

theorem BlockPtr.getLastOp!_OperationPtr_linkBetweenWithParent {block : BlockPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getLastOp! newCtx = if parent = block ∧ next = none then some op' else block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent
  | grind [BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockPtr.lastOp!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).lastOp

theorem OperationPtr.prev!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).prev =
    if operation = next then
      some op'
    else if operation = op' then
      prev
    else
      (operation.get! ctx).prev := by
  grind

theorem OperationPtr.getPrevOp!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getPrevOp! newCtx = if operation = next then some op' else if operation = op' then prev else operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.prev!_OperationPtr_linkBetweenWithParent
  | grind [OperationPtr.prev!_OperationPtr_linkBetweenWithParent]

grind_pattern OperationPtr.prev!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).prev

theorem OperationPtr.next!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).next =
    if operation = prev then
      some op'
    else if operation = op' then
      next
    else
      (operation.get! ctx).next := by
  grind

theorem OperationPtr.getNextOp!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getNextOp! newCtx = if operation = prev then some op' else if operation = op' then next else operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.next!_OperationPtr_linkBetweenWithParent
  | grind [OperationPtr.next!_OperationPtr_linkBetweenWithParent]

grind_pattern OperationPtr.next!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).next

theorem OperationPtr.parent!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).parent =
    if operation = op' then
      some parent
    else
      (operation.get! ctx).parent := by
  grind

theorem OperationPtr.getParent!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getParent! newCtx = if operation = op' then some parent else operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.parent!_OperationPtr_linkBetweenWithParent
  | grind [OperationPtr.parent!_OperationPtr_linkBetweenWithParent]

grind_pattern OperationPtr.parent!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).parent

@[simp]
theorem OperationPtr.getOpType!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.getOpType! newCtx) = (operation.getOpType! ctx) := by
  grind

grind_pattern OperationPtr.getOpType!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.getOpType! newCtx)

@[simp]
theorem OperationPtr.attrs!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx).attrs = (operation.get! ctx).attrs := by
  grind

@[simp]
theorem OperationPtr.getAttributes!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.attrs!_OperationPtr_linkBetweenWithParent
  | grind [OperationPtr.attrs!_OperationPtr_linkBetweenWithParent]

grind_pattern OperationPtr.attrs!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (operation.get! newCtx).attrs

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
theorem OpResultPtr.get!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  grind

@[simp]
theorem OpResultPtr.getOwner!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpResultPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem OpResultPtr.getFirstUse!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpResultPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem OpResultPtr.getType!_OperationPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpResultPtr.get!_OperationPtr_linkBetweenWithParent]

grind_pattern OpResultPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent {operation : OperationPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem OpOperandPtr.getValue!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem OpOperandPtr.getOwner!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem OpOperandPtr.getBack!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem OpOperandPtr.getNextUse!_OperationPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_OperationPtr_linkBetweenWithParent]

grind_pattern OpOperandPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

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
theorem BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem BlockOperandPtr.getValue!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem BlockOperandPtr.getOwner!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem BlockOperandPtr.getBack!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem BlockOperandPtr.getNextUse!_OperationPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockOperandPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

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
theorem BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

@[simp]
theorem BlockArgumentPtr.getOwner!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem BlockArgumentPtr.getIndex!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem BlockArgumentPtr.getType!_OperationPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent]

grind_pattern BlockArgumentPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    region.get! newCtx = region.get! ctx := by
  grind

@[simp]
theorem RegionPtr.getLastBlock!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getLastBlock! newCtx = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [RegionPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem RegionPtr.getFirstBlock!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getFirstBlock! newCtx = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [RegionPtr.get!_OperationPtr_linkBetweenWithParent]

@[simp]
theorem RegionPtr.getParent!_OperationPtr_linkBetweenWithParent {region : RegionPtr} :
    op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_OperationPtr_linkBetweenWithParent
  | grind [RegionPtr.get!_OperationPtr_linkBetweenWithParent]

grind_pattern RegionPtr.get!_OperationPtr_linkBetweenWithParent =>
  op'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, region.get! newCtx

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
theorem BlockPtr.firstUse!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).firstUse =
    (block.get! ctx).firstUse := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).prev =
    if block =  next then
      some block'
    else if block = block' then
      prev
    else
      (block.get! ctx).prev := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getPrevBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = if block = next then some block' else if block = block' then prev else block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).next =
    if block =  prev then
      some block'
    else if block = block' then
      next
    else
      (block.get! ctx).next := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getNextBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = if block = prev then some block' else if block = block' then next else block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).parent =
    (block.get! ctx).parent := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getParent! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).firstOp =
    (block.get! ctx).firstOp := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getFirstOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_linkBetween {block : BlockPtr} :
    (block.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn)).lastOp =
    (block.get! ctx).lastOp := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_linkBetween {block : BlockPtr} :
    block.getLastOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getRegions! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getRegions! ctx := by
  simp only [OperationPtr.getRegions!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getAttributes! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getParent! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getPrevOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNextOp! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetween
  | grind

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
theorem OpResultPtr.get!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opResult.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_linkBetween {opResult : OpResultPtr} :
    opResult.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetween {operation : OperationPtr} :
    operation.getNumOperands! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    operation.getNumOperands! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    opOperandPtr.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getValue! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getBack! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_linkBetween {opOperandPtr : OpOperandPtr} :
    opOperandPtr.getNextUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = opOperandPtr.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetween
  | grind

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
theorem BlockOperandPtr.get!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockOperand.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_linkBetween {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetween
  | grind

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
theorem BlockArgumentPtr.get!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    blockArg.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_linkBetween {blockArg : BlockArgumentPtr} :
    blockArg.getType! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_linkBetween {region : RegionPtr} :
    region.get! (block'.linkBetween ctx prev next selfIn prevIn nextIn) =
    region.get! ctx := by
  simp only [BlockPtr.linkBetween]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_linkBetween {region : RegionPtr} :
    region.getLastBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_linkBetween {region : RegionPtr} :
    region.getFirstBlock! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_BlockPtr_linkBetween
  | grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_linkBetween {region : RegionPtr} :
    region.getParent! (block'.linkBetween ctx prev next selfIn prevIn nextIn) = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_BlockPtr_linkBetween
  | grind

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
theorem BlockPtr.parent!_of_BlockPtr_setParentWithCheck_eq :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block'.get! ctx).parent = none := by
  grind

@[grind →]
theorem BlockPtr.getParent!_of_BlockPtr_setParentWithCheck_eq :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block'.getParent! ctx = none := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_of_BlockPtr_setParentWithCheck_eq
  | grind

theorem BlockPtr.firstUse!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse := by
  grind

theorem BlockPtr.getFirstUse!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_BlockPtr_setParentWithCheck
  | grind [BlockPtr.firstUse!_BlockPtr_setParentWithCheck]

grind_pattern BlockPtr.firstUse!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).firstUse

theorem BlockPtr.prev!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).prev = (block.get! ctx).prev := by
  grind

theorem BlockPtr.getPrevBlock!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getPrevBlock! newCtx = block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_BlockPtr_setParentWithCheck
  | grind [BlockPtr.prev!_BlockPtr_setParentWithCheck]

grind_pattern BlockPtr.prev!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).prev

theorem BlockPtr.next!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).next = (block.get! ctx).next := by
  grind

theorem BlockPtr.getNextBlock!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getNextBlock! newCtx = block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_BlockPtr_setParentWithCheck
  | grind [BlockPtr.next!_BlockPtr_setParentWithCheck]

grind_pattern BlockPtr.next!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).next

theorem BlockPtr.parent!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).parent =
    if block = block' then
      some newParent
    else
      (block.get! ctx).parent := by
  grind

theorem BlockPtr.getParent!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getParent! newCtx = if block = block' then some newParent else block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_BlockPtr_setParentWithCheck
  | grind [BlockPtr.parent!_BlockPtr_setParentWithCheck]

grind_pattern BlockPtr.parent!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).firstOp = (block.get! ctx).firstOp := by
  grind

theorem BlockPtr.getFirstOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_BlockPtr_setParentWithCheck
  | grind [BlockPtr.firstOp!_BlockPtr_setParentWithCheck]

grind_pattern BlockPtr.firstOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    (block.get! newCtx).lastOp = (block.get! ctx).lastOp := by
  grind

theorem BlockPtr.getLastOp!_BlockPtr_setParentWithCheck {block : BlockPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_BlockPtr_setParentWithCheck
  | grind [BlockPtr.lastOp!_BlockPtr_setParentWithCheck]

grind_pattern BlockPtr.lastOp!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, (block.get! newCtx).lastOp

@[simp]
theorem OperationPtr.get!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.get! newCtx = operation.get! ctx := by
  grind

@[simp]
theorem OperationPtr.getRegions!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getRegions! newCtx = operation.getRegions! ctx := by
  simp only [OperationPtr.getRegions!_def]
  first
  | exact OperationPtr.get!_BlockPtr_setParentWithCheck
  | grind [OperationPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OperationPtr.getAttributes!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.get!_BlockPtr_setParentWithCheck
  | grind [OperationPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OperationPtr.getParent!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getParent! newCtx = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.get!_BlockPtr_setParentWithCheck
  | grind [OperationPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OperationPtr.getPrevOp!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.get!_BlockPtr_setParentWithCheck
  | grind [OperationPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OperationPtr.getNextOp!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.get!_BlockPtr_setParentWithCheck
  | grind [OperationPtr.get!_BlockPtr_setParentWithCheck]

grind_pattern OperationPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.get! newCtx

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
theorem OpResultPtr.get!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  grind

@[simp]
theorem OpResultPtr.getOwner!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpResultPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OpResultPtr.getFirstUse!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpResultPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OpResultPtr.getType!_BlockPtr_setParentWithCheck {opResult : OpResultPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpResultPtr.get!_BlockPtr_setParentWithCheck]

grind_pattern OpResultPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck {operation : OperationPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem OpOperandPtr.getValue!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OpOperandPtr.getOwner!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OpOperandPtr.getBack!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem OpOperandPtr.getNextUse!_BlockPtr_setParentWithCheck {operand : OpOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [OpOperandPtr.get!_BlockPtr_setParentWithCheck]

grind_pattern OpOperandPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

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
theorem BlockOperandPtr.get!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem BlockOperandPtr.getValue!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem BlockOperandPtr.getOwner!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem BlockOperandPtr.getBack!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setParentWithCheck {operand : BlockOperandPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockOperandPtr.get!_BlockPtr_setParentWithCheck]

grind_pattern BlockOperandPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, operand.get! newCtx

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
theorem BlockArgumentPtr.get!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

@[simp]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem BlockArgumentPtr.getType!_BlockPtr_setParentWithCheck {blockArg : BlockArgumentPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_setParentWithCheck
  | grind [BlockArgumentPtr.get!_BlockPtr_setParentWithCheck]

grind_pattern BlockArgumentPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.get!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx →
    region.get! newCtx = region.get! ctx := by
  grind

@[simp]
theorem RegionPtr.getLastBlock!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getLastBlock! newCtx = region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.get!_BlockPtr_setParentWithCheck
  | grind [RegionPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem RegionPtr.getFirstBlock!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getFirstBlock! newCtx = region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.get!_BlockPtr_setParentWithCheck
  | grind [RegionPtr.get!_BlockPtr_setParentWithCheck]

@[simp]
theorem RegionPtr.getParent!_BlockPtr_setParentWithCheck {region : RegionPtr} :
    block'.setParentWithCheck ctx newParent selfIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.get!_BlockPtr_setParentWithCheck
  | grind [RegionPtr.get!_BlockPtr_setParentWithCheck]

grind_pattern RegionPtr.get!_BlockPtr_setParentWithCheck =>
  block'.setParentWithCheck ctx newParent selfIn, some newCtx, region.get! newCtx

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
theorem BlockPtr.parent!_of_BlockPtr_linkBetweenWithParent_eq :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block'.get! ctx).parent = none := by
  grind

@[grind →]
theorem BlockPtr.getParent!_of_BlockPtr_linkBetweenWithParent_eq :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block'.getParent! ctx = none := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_of_BlockPtr_linkBetweenWithParent_eq
  | grind

@[simp]
theorem BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstUse = (block.get! ctx).firstUse
    := by
  grind

@[simp]
theorem BlockPtr.getFirstUse!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstUse! newCtx = block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  first
  | exact BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent
  | grind [BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockPtr.firstUse!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstUse

theorem BlockPtr.prev!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).prev =
    if block = next then
      some block'
    else if block = block' then
      prev
    else
      (block.get! ctx).prev := by
  grind

theorem BlockPtr.getPrevBlock!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getPrevBlock! newCtx = if block = next then some block' else if block = block' then prev else block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  first
  | exact BlockPtr.prev!_BlockPtr_linkBetweenWithParent
  | grind [BlockPtr.prev!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockPtr.prev!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).prev

@[simp]
theorem BlockPtr.next!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).next =
      if block =  prev then
        some block'
      else if block = block' then
        next
      else
        (block.get! ctx).next := by
  grind

@[simp]
theorem BlockPtr.getNextBlock!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getNextBlock! newCtx = if block = prev then some block' else if block = block' then next else block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  first
  | exact BlockPtr.next!_BlockPtr_linkBetweenWithParent
  | grind [BlockPtr.next!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockPtr.next!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).next

@[simp]
theorem BlockPtr.parent!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).parent =
      if block = block' then
        some parent
      else
        (block.get! ctx).parent := by
  grind

@[simp]
theorem BlockPtr.getParent!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getParent! newCtx = if block = block' then some parent else block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  first
  | exact BlockPtr.parent!_BlockPtr_linkBetweenWithParent
  | grind [BlockPtr.parent!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockPtr.parent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).parent

theorem BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).firstOp = (block.get! ctx).firstOp := by
  grind

theorem BlockPtr.getFirstOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getFirstOp! newCtx = block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  first
  | exact BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent
  | grind [BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockPtr.firstOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).firstOp

theorem BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (block.get! newCtx).lastOp = (block.get! ctx).lastOp := by
  grind

theorem BlockPtr.getLastOp!_BlockPtr_linkBetweenWithParent {block : BlockPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → block.getLastOp! newCtx = block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  first
  | exact BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent
  | grind [BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockPtr.lastOp!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (block.get! newCtx).lastOp

theorem OperationPtr.get!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (operation.get! newCtx) = operation.get! ctx := by
  grind

theorem OperationPtr.getRegions!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getRegions! newCtx = operation.getRegions! ctx := by
  simp only [OperationPtr.getRegions!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OperationPtr.get!_BlockPtr_linkBetweenWithParent]

theorem OperationPtr.getAttributes!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getAttributes! newCtx = operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OperationPtr.get!_BlockPtr_linkBetweenWithParent]

theorem OperationPtr.getParent!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getParent! newCtx = operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OperationPtr.get!_BlockPtr_linkBetweenWithParent]

theorem OperationPtr.getPrevOp!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getPrevOp! newCtx = operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OperationPtr.get!_BlockPtr_linkBetweenWithParent]

theorem OperationPtr.getNextOp!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operation.getNextOp! newCtx = operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  first
  | exact OperationPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OperationPtr.get!_BlockPtr_linkBetweenWithParent]

grind_pattern OperationPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.get! newCtx

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
theorem OpResultPtr.get!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    opResult.get! newCtx = opResult.get! ctx := by
  unfold BlockPtr.linkBetweenWithParent
  grind

@[simp]
theorem OpResultPtr.getOwner!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getOwner! newCtx = opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpResultPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem OpResultPtr.getFirstUse!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getFirstUse! newCtx = opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpResultPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem OpResultPtr.getType!_BlockPtr_linkBetweenWithParent {opResult : OpResultPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → opResult.getType! newCtx = opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  first
  | exact OpResultPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpResultPtr.get!_BlockPtr_linkBetweenWithParent]

grind_pattern OpResultPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, opResult.get! newCtx

@[simp]
theorem OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent {operation : OperationPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operation.getNumOperands! newCtx = operation.getNumOperands! ctx := by
  grind

grind_pattern OperationPtr.getNumOperands!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operation.getNumOperands! newCtx

@[simp]
theorem OpOperandPtr.get!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem OpOperandPtr.getValue!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem OpOperandPtr.getOwner!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem OpOperandPtr.getBack!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem OpOperandPtr.getNextUse!_BlockPtr_linkBetweenWithParent {operand : OpOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  first
  | exact OpOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [OpOperandPtr.get!_BlockPtr_linkBetweenWithParent]

grind_pattern OpOperandPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

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
theorem BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    operand.get! newCtx = operand.get! ctx := by
  grind

@[simp]
theorem BlockOperandPtr.getValue!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getValue! newCtx = operand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem BlockOperandPtr.getOwner!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getOwner! newCtx = operand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem BlockOperandPtr.getBack!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getBack! newCtx = operand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem BlockOperandPtr.getNextUse!_BlockPtr_linkBetweenWithParent {operand : BlockOperandPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → operand.getNextUse! newCtx = operand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  first
  | exact BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockOperandPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, operand.get! newCtx

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
theorem BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    blockArg.get! newCtx = blockArg.get! ctx := by
  grind

@[simp]
theorem BlockArgumentPtr.getOwner!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getOwner! newCtx = blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem BlockArgumentPtr.getIndex!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getIndex! newCtx = blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getFirstUse! newCtx = blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent]

@[simp]
theorem BlockArgumentPtr.getType!_BlockPtr_linkBetweenWithParent {blockArg : BlockArgumentPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → blockArg.getType! newCtx = blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  first
  | exact BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent
  | grind [BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent]

grind_pattern BlockArgumentPtr.get!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, blockArg.get! newCtx

@[simp]
theorem RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx).firstBlock =
      if prev = none ∧ region = parent then
        some block'
      else
        (region.get! ctx).firstBlock := by
  grind

@[simp]
theorem RegionPtr.getFirstBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getFirstBlock! newCtx = if prev = none ∧ region = parent then some block' else region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  first
  | exact RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent
  | grind [RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent]

grind_pattern RegionPtr.firstBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx).firstBlock

@[simp]
theorem RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx).lastBlock =
      if next = none ∧ region = parent then
        some block'
      else
        (region.get! ctx).lastBlock := by
  grind

@[simp]
theorem RegionPtr.getLastBlock!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getLastBlock! newCtx = if next = none ∧ region = parent then some block' else region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  first
  | exact RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent
  | grind [RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent]

grind_pattern RegionPtr.lastBlock!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx).lastBlock

@[simp]
theorem RegionPtr.parent!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx →
    (region.get! newCtx).parent = (region.get! ctx).parent := by
  grind

@[simp]
theorem RegionPtr.getParent!_BlockPtr_linkBetweenWithParent {region : RegionPtr} :
    block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn = some newCtx → region.getParent! newCtx = region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  first
  | exact RegionPtr.parent!_BlockPtr_linkBetweenWithParent
  | grind [RegionPtr.parent!_BlockPtr_linkBetweenWithParent]

grind_pattern RegionPtr.parent!_BlockPtr_linkBetweenWithParent =>
  block'.linkBetweenWithParent ctx prev next parent selfIn prevIn nextIn parentIn, some newCtx, (region.get! newCtx).parent

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
