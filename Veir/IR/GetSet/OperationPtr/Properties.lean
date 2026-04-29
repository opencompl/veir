module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.setProperties -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setProperties {block : BlockPtr} :
    block.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    if operation = operation' then
      { operation.get! ctx with opType := (operation'.get! ctx).opType, properties := newProperties }
    else
      operation.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getProperties!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setProperties (opCode := opCode') operation' ctx newProperties inBounds hprop) opCode =
    if operation = operation' then
      if h : opCode = opCode' then
        h ▸ newProperties
      else
        default
    else
      operation.getProperties! ctx opCode := by
  grind

/- We probably do not want both this lemma and the previous one to be grind.
  TODO: make a decision about this
-/
@[grind =]
theorem OperationPtr.getProperties!_OperationPtr_setProperties_same_opCode {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setProperties (opCode := opCode) operation' ctx newProperties inBounds hprop) opCode =
    if operation = operation' then
      newProperties
    else
      operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setProperties {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setProperties {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setProperties {region : RegionPtr} :
    region.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setProperties {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setProperties {value : ValuePtr} :
    value.getType! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setProperties {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setProperties operation' ctx newProperties inBounds hprop) =
    opOperandPtr.get! ctx := by
  grind

/- OperationPtr.setAttributes -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setAttributes {block : BlockPtr} :
    block.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    if operation = operation' then
      { operation.get! ctx with attrs := newAttrs }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setAttributes {operation : OperationPtr} :
    (operation.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setAttributes {operation : OperationPtr} :
    (operation.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setAttributes {operation : OperationPtr} :
    (operation.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setAttributes {operation : OperationPtr} :
    (operation.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn)).opType =
    (operation.get! ctx).opType := by
  grind

@[grind =]
theorem OperationPtr.attrs!_OperationPtr_setAttributes {operation : OperationPtr} :
    (operation.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn)).attrs =
    if operation = operation' then
      newAttrs
    else
      (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setAttributes operation' ctx newAttrs opIn) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setAttributes operation' ctx newAttrs opIn) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setAttributes {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setAttributes {region : RegionPtr} :
    region.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setAttributes {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setAttributes {value : ValuePtr} :
    value.getType! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setAttributes {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opOperandPtr.get! ctx := by
  grind

