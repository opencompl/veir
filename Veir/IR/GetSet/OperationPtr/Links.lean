module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.setNextOp -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setNextOp {block : BlockPtr} :
    block.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    if op' = operation then
      { operation.get! ctx with next := newNextOp }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setNextOp op' ctx newNextOp hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setNextOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[grind =]
theorem OperationPtr.next!_OperationPtr_setNextOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop')).next =
    if operation = op' then
      newNextOp
    else
      (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setNextOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setNextOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setNextOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setNextOp op' ctx hop' newNextOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setNextOp op' ctx hop' newNextOp) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setNextOp op' ctx hop' newNextOp) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setNextOp op' ctx hop' newNextOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setNextOp op' ctx newNextOp hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setNextOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setNextOp {arg : BlockArgumentPtr} :
    arg.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setNextOp {region : RegionPtr} :
    region.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setNextOp {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setNextOp {value : ValuePtr} :
    value.getType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setNextOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperandPtr.get! ctx := by
  grind


/- OperationPtr.setPrevOp -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    if op' = operation then
      { operation.get! ctx with prev := newPrevOp }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setPrevOp op' ctx newPrevOp hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[grind =]
theorem OperationPtr.prev!_OperationPtr_setPrevOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop')).prev =
    if operation = op' then
      newPrevOp
    else
      (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setPrevOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setPrevOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setPrevOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setPrevOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setPrevOp op' ctx hop' newPrevOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setPrevOp op' ctx hop' newPrevOp) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setPrevOp op' ctx hop' newPrevOp) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setPrevOp op' ctx hop' newPrevOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setPrevOp op' ctx newPrevOp hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setPrevOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setPrevOp {arg : BlockArgumentPtr} :
    arg.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setPrevOp {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setPrevOp {value : ValuePtr} :
    value.getType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setPrevOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperandPtr.get! ctx := by
  grind

/- OperationPtr.setParent -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setParent {block : BlockPtr} :
    block.get! (OperationPtr.setParent op' ctx newParent hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setParent {operation : OperationPtr} :
    operation.get! (OperationPtr.setParent op' ctx newParent hop') =
    if op' = operation then
      { operation.get! ctx with parent := newParent }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setParent op' ctx newParent hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setParent {operation : OperationPtr} :
    (operation.get! (OperationPtr.setParent op' ctx newParent hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setParent {operation : OperationPtr} :
    (operation.get! (OperationPtr.setParent op' ctx newParent hop')).next =
    (operation.get! ctx).next := by
  grind

@[grind =]
theorem OperationPtr.parent!_OperationPtr_setParent {operation : OperationPtr} :
    (operation.get! (OperationPtr.setParent op' ctx newParent hop')).parent =
    if operation = op' then
      newParent
    else
      (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setParent {operation : OperationPtr} :
    (operation.get! (OperationPtr.setParent op' ctx newParent hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setParent {operation : OperationPtr} :
    (operation.get! (OperationPtr.setParent op' ctx newParent hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setParent op' ctx hop' newParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setParent op' ctx hop' newParent) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setParent op' ctx hop' newParent) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setParent op' ctx hop' newParent) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setParent op' ctx newParent hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setParent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setParent {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setParent op' ctx newParent hop') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setParent {arg : BlockArgumentPtr} :
    arg.get! (OperationPtr.setParent op' ctx newParent hop') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setParent {region : RegionPtr} :
    region.get! (OperationPtr.setParent op' ctx newParent hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setParent {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setParent {value : ValuePtr} :
    value.getType! (OperationPtr.setParent op' ctx newParent hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setParent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setParent op' ctx newParent hop') =
    opOperandPtr.get! ctx := by
  grind

