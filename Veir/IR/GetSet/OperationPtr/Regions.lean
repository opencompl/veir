module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.setRegions -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setRegions {block : BlockPtr} :
    block.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    if operation = operation' then
      { operation.get! ctx with regions := newRegions }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setRegions operation' ctx newRegions hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setRegions {operation : OperationPtr} :
    (operation.get! (OperationPtr.setRegions operation' ctx newRegions hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setRegions {operation : OperationPtr} :
    (operation.get! (OperationPtr.setRegions operation' ctx newRegions hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setRegions {operation : OperationPtr} :
    (operation.get! (OperationPtr.setRegions operation' ctx newRegions hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setRegions {operation : OperationPtr} :
    (operation.get! (OperationPtr.setRegions operation' ctx newRegions hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setRegions {operation : OperationPtr} :
    (operation.get! (OperationPtr.setRegions operation' ctx newRegions hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setRegions operation' ctx hop' newRegions) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setRegions operation' ctx hop' newRegions) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setRegions operation' ctx hop' newRegions) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperand.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setRegions operation' ctx newRegions hop') =
    if operation = operation' then
      newRegions.size
    else
      operation.getNumRegions! ctx := by
  grind

@[grind =]
theorem OperationPtr.getRegion!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setRegions operation' ctx newRegions hop') index =
    if operation = operation' then
      newRegions[index]!
    else
      operation.getRegion! ctx index := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setRegions {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setRegions {block : BlockPtr} {hop} :
    block.getNumArguments! (OperationPtr.setRegions op ctx newRegions hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setRegions {region : RegionPtr} :
    region.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setRegions {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setRegions operation' ctx newRegions hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setRegions {value : ValuePtr} :
    value.getType! (OperationPtr.setRegions operation' ctx newRegions hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setRegions {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opOperandPtr.get! ctx := by
  grind


/- OperationPtr.setRegions -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_pushRegion {block : BlockPtr} :
    block.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    if operation = operation' then
      { operation.get! ctx with regions := (operation.get! ctx).regions.push newRegion }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_pushRegion {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushRegion operation' ctx newRegion hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_pushRegion {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushRegion operation' ctx newRegion hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_pushRegion {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushRegion operation' ctx newRegion hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_pushRegion {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushRegion operation' ctx newRegion hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_pushRegion {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushRegion operation' ctx newRegion hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushRegion operation' ctx newRegion hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.pushRegion operation' ctx hop' newRegion) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushRegion operation' ctx hop' newRegion) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.pushRegion operation' ctx hop' newRegion) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockOperand.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    if operation = operation' then
      operation.getNumRegions! ctx + 1
    else
      operation.getNumRegions! ctx := by
  grind

@[grind =]
theorem OperationPtr.getRegion!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.pushRegion operation' ctx newRegion hop') index =
    if operation = operation' ∧ index = operation.getNumRegions! ctx then
      newRegion
    else
      operation.getRegion! ctx index := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_pushRegion {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_pushRegion {block : BlockPtr} {hop} :
    block.getNumArguments! (OperationPtr.pushRegion op ctx newRegion hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_pushRegion {region : RegionPtr} :
    region.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_pushRegion {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_pushRegion {value : ValuePtr} :
    value.getType! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_pushRegion {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opOperandPtr.get! ctx := by
  grind


