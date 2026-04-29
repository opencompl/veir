module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- BlockOperandPtr.setNextUse -/

@[simp, grind =]
theorem BlockPtr.get!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with blockOperands :=
        (operation.get! ctx).blockOperands.set! operand'.index { operand'.get! ctx with nextUse := newNextUse } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_setNextUse {operand : OpOperandPtr} :
    operand.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getOperands! (BlockOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if blockOperand = operand' then
      { blockOperand.get! ctx with nextUse := newNextUse }
    else
      blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumRegions! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getRegion! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_setNextUse {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if blockOperandPtr = .blockOperandNextUse operand' then
      newNextUse
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getNumArguments! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_setNextUse {value : ValuePtr} :
    value.getFirstUse! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_setNextUse {value : ValuePtr} :
    value.getType! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_setNextUse {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opOperandPtr.get! ctx := by
  grind

/- BlockOperandPtr.setBack -/

@[simp, grind =]
theorem BlockPtr.get!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with blockOperands :=
        (operation.get! ctx).blockOperands.set! operand'.index { operand'.get! ctx with back := newBack } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setBack operand' ctx newBack hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_BlockOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_setBack {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getOperands! (BlockOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    if blockOperand = operand' then
      { blockOperand.get! ctx with back := newBack }
    else
      blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumRegions! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getRegion! (BlockOperandPtr.setBack operand' ctx newBack hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_setBack {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getNumArguments! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_setBack {value : ValuePtr} :
    value.getFirstUse! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_setBack {value : ValuePtr} :
    value.getType! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_setBack {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperandPtr.get! ctx := by
  grind


/- BlockOperandPtr.setOwner -/

@[simp, grind =]
theorem BlockPtr.get!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with blockOperands :=
        (operation.get! ctx).blockOperands.set! operand'.index { operand'.get! ctx with owner := newOwner } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getOperands! (BlockOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    if blockOperand = operand' then
      { blockOperand.get! ctx with owner := newOwner }
    else
      blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumRegions! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getRegion! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_setOwner {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getNumArguments! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_setOwner {value : ValuePtr} :
    value.getFirstUse! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_setOwner {value : ValuePtr} :
    value.getType! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_setOwner {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperandPtr.get! ctx := by
  grind


/- BlockOperandPtr.setValue -/

@[simp, grind =]
theorem BlockPtr.get!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    if operand'.op = operation then
      {operation.get! ctx with blockOperands :=
        (operation.get! ctx).blockOperands.set! operand'.index { operand'.get! ctx with value := newValue } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setValue operand' ctx newValue hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_BlockOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtr_setValue {operation : OperationPtr} :
    (operation.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getOperands! (BlockOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    if blockOperand = operand' then
      { blockOperand.get! ctx with value := newValue }
    else
      blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumRegions! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getRegion! (BlockOperandPtr.setValue operand' ctx newValue hoperand') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtr_setValue {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getNumArguments! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtr_setValue {value : ValuePtr} :
    value.getFirstUse! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtr_setValue {value : ValuePtr} :
    value.getType! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtr_setValue {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperandPtr.get! ctx := by
  grind

