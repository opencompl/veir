module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OpOperandPtr.setNextUse -/

@[simp, grind =]
theorem BlockPtr.get!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with operands :=
        (operation.get! ctx).operands.set! operand'.index { operand'.get! ctx with nextUse := newNextUse } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if opOperand = operand' then
      { opOperand.get! ctx with nextUse := newNextUse }
    else
      opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getOperands! (OpOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumSuccessors! (OpOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumRegions! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getRegion! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_setNextUse {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getNumArguments! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_setNextUse {value : ValuePtr} :
    value.getFirstUse! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_setNextUse {value : ValuePtr} :
    value.getType! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_setNextUse {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if opOperandPtr = OpOperandPtrPtr.operandNextUse operand' then
      newNextUse
    else
      opOperandPtr.get! ctx := by
  grind

/- OpOperandPtr.setBack -/

@[simp, grind =]
theorem BlockPtr.get!_OpOperandPtr_setBack {block : BlockPtr} :
    block.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with operands :=
        (operation.get! ctx).operands.set! operand'.index { operand'.get! ctx with back := newBack } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setBack operand' ctx newBack hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setBack operand' ctx newBack hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setBack operand' ctx newBack hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setBack operand' ctx newBack hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setBack operand' ctx newBack hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setBack operand' ctx newBack hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    if opOperand = operand' then
      { opOperand.get! ctx with back := newBack }
    else
      opOperand.get! ctx := by
  split <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getOperands! (OpOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumSuccessors! (OpOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumRegions! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getRegion! (OpOperandPtr.setBack operand' ctx newBack hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_setBack {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getNumArguments! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setBack {region : RegionPtr} :
    region.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_setBack {value : ValuePtr} :
    value.getFirstUse! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_setBack {value : ValuePtr} :
    value.getType! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_setBack {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperandPtr.get! ctx := by
  grind


/- OpOperandPtr.setOwner -/

@[simp, grind =]
theorem BlockPtr.get!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with operands :=
        (operation.get! ctx).operands.set! operand'.index { operand'.get! ctx with owner := newOwner } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    if opOperand = operand' then
      { opOperand.get! ctx with owner := newOwner }
    else
      opOperand.get! ctx := by
  split <;> grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getOperands! (OpOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumSuccessors! (OpOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumRegions! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getRegion! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_setOwner {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getNumArguments! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_setOwner {value : ValuePtr} :
    value.getFirstUse! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_setOwner {value : ValuePtr} :
    value.getType! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_setOwner {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperandPtr.get! ctx := by
  grind

/- OpOperandPtr.setValue -/

@[simp, grind =]
theorem BlockPtr.get!_OpOperandPtr_setValue {block : BlockPtr} :
    block.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with operands :=
        (operation.get! ctx).operands.set! operand'.index { operand'.get! ctx with value := newValue } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setValue operand' ctx newValue hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setValue operand' ctx newValue hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setValue operand' ctx newValue hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setValue operand' ctx newValue hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setValue operand' ctx newValue hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (OpOperandPtr.setValue operand' ctx newValue hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    if opOperand = operand' then
      { opOperand.get! ctx with value := newValue }
    else
      opOperand.get! ctx := by
  split <;> grind

@[grind =]
theorem OperationPtr.getOperands!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getOperands! (OpOperandPtr.setValue operand' ctx hoperand' newValue) =
    if operation = operand'.op then
      (operation.getOperands! ctx).set! operand'.index hoperand'
    else
      operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumSuccessors! (OpOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumRegions! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getRegion! (OpOperandPtr.setValue operand' ctx newValue hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_setValue {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getNumArguments! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setValue {region : RegionPtr} :
    region.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_setValue {value : ValuePtr} :
    value.getFirstUse! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_setValue {value : ValuePtr} :
    value.getType! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_setValue {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperandPtr.get! ctx := by
  grind

