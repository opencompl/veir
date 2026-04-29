module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- ValuePtr.setType -/

@[grind =]
theorem BlockPtr.get!_ValuePtr_setType {block : BlockPtr} :
    block.get! (ValuePtr.setType value' ctx newType hvalue') =
    match value' with
    | ValuePtr.opResult _ => block.get! ctx
    | ValuePtr.blockArgument ba =>
      if ba.block = block then
        { block.get! ctx with arguments :=
          (block.get! ctx).arguments.set! ba.index { ba.get! ctx with type := newType } }
      else
        block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_ValuePtr_setType {block : BlockPtr} :
    (block.get! (ValuePtr.setType value' ctx newType hvalue')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_ValuePtr_setType {block : BlockPtr} :
    (block.get! (ValuePtr.setType value' ctx newType hvalue')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_ValuePtr_setType {block : BlockPtr} :
    (block.get! (ValuePtr.setType value' ctx newType hvalue')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_ValuePtr_setType {block : BlockPtr} :
    (block.get! (ValuePtr.setType value' ctx newType hvalue')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_ValuePtr_setType {block : BlockPtr} :
    (block.get! (ValuePtr.setType value' ctx newType hvalue')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_ValuePtr_setType {block : BlockPtr} :
    (block.get! (ValuePtr.setType value' ctx newType hvalue')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_ValuePtr_setType {operation : OperationPtr} :
    operation.get! (ValuePtr.setType value' ctx newType hvalue') =
    match value' with
    | ValuePtr.opResult or =>
      if or.op = operation then
        {operation.get! ctx with results :=
          (operation.get! ctx).results.set! or.index { or.get! ctx with type := newType } }
      else
        operation.get! ctx
    | ValuePtr.blockArgument _ => operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_ValuePtr_setType {operation : OperationPtr} :
    operation.getProperties! (ValuePtr.setType value' ctx newType hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_ValuePtr_setType {operation : OperationPtr} :
    (operation.get! (ValuePtr.setType value' ctx newType hvalue')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_ValuePtr_setType {operation : OperationPtr} :
    (operation.get! (ValuePtr.setType value' ctx newType hvalue')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_ValuePtr_setType {operation : OperationPtr} :
    (operation.get! (ValuePtr.setType value' ctx newType hvalue')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_ValuePtr_setType {operation : OperationPtr} :
    (operation.get! (ValuePtr.setType value' ctx newType hvalue')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_ValuePtr_setType {operation : OperationPtr} :
    (operation.get! (ValuePtr.setType value' ctx newType hvalue')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_ValuePtr_setType {operation : OperationPtr} :
    (operation.get! (ValuePtr.setType value' ctx newType hvalue')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNumResults! (ValuePtr.setType value' ctx hvalue' newType) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.get! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = ValuePtr.opResult opResult then
      { opResult.get! ctx with type := newType }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNumOperands! (ValuePtr.setType value' ctx hvalue' newType) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.get! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_ValuePtr_setType {operation : OperationPtr} :
    operation.getOperands! (ValuePtr.setType value' ctx hvalue' newType) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNumSuccessors! (ValuePtr.setType value' ctx hvalue' newType) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.get! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNumRegions! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_ValuePtr_setType {operation : OperationPtr} :
    operation.getRegion! (ValuePtr.setType value' ctx newType hvalue') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_ValuePtr_setType {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_ValuePtr_setType {block : BlockPtr} :
    block.getNumArguments! (ValuePtr.setType value' ctx newType hvalue') =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_ValuePtr_setType {arg : BlockArgumentPtr} :
    arg.get! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = ValuePtr.blockArgument arg then
      { arg.get! ctx with type := newType }
    else
      arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_ValuePtr_setType {region : RegionPtr} :
    region.get! (ValuePtr.setType value' ctx newType hvalue') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_ValuePtr_setType {value : ValuePtr} :
    value.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_ValuePtr_setType {value : ValuePtr} :
    value.getType! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = value then
      newType
    else
      value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_ValuePtr_setType {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (ValuePtr.setType value' ctx newType hvalue') =
    opOperandPtr.get! ctx := by
  grind

/- ValuePtr.setFirstUse -/

@[grind =]
theorem BlockPtr.get!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    match value' with
    | ValuePtr.opResult _ => block.get! ctx
    | ValuePtr.blockArgument ba =>
      if ba.block = block then
        { block.get! ctx with arguments :=
          (block.get! ctx).arguments.set! ba.index { ba.get! ctx with firstUse := newFirstUse } }
      else
        block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_ValuePtr_setFirstUse {block : BlockPtr} :
    (block.get! (ValuePtr.setFirstUse value' ctx newType hvalue')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_ValuePtr_setFirstUse {block : BlockPtr} :
    (block.get! (ValuePtr.setFirstUse value' ctx newType hvalue')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_ValuePtr_setFirstUse {block : BlockPtr} :
    (block.get! (ValuePtr.setFirstUse value' ctx newType hvalue')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_ValuePtr_setFirstUse {block : BlockPtr} :
    (block.get! (ValuePtr.setFirstUse value' ctx newType hvalue')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_ValuePtr_setFirstUse {block : BlockPtr} :
    (block.get! (ValuePtr.setFirstUse value' ctx newType hvalue')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_ValuePtr_setFirstUse {block : BlockPtr} :
    (block.get! (ValuePtr.setFirstUse value' ctx newType hvalue')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    match value' with
    | ValuePtr.opResult or =>
      if or.op = operation then
        {operation.get! ctx with results :=
          (operation.get! ctx).results.set! or.index { or.get! ctx with firstUse := newFirstUse } }
      else
        operation.get! ctx
    | ValuePtr.blockArgument _ => operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getProperties! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_ValuePtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_ValuePtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_ValuePtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_ValuePtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_ValuePtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_ValuePtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNumResults! (ValuePtr.setFirstUse value' ctx hvalue' newFirstUse) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = ValuePtr.opResult opResult then
      { opResult.get! ctx with firstUse := newFirstUse }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (ValuePtr.setFirstUse value' ctx hvalue' newFirstUse) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getOperands! (ValuePtr.setFirstUse value' ctx hvalue' newFirstUse) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNumSuccessors! (ValuePtr.setFirstUse value' ctx hvalue' newFirstUse) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNumRegions! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getRegion! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_ValuePtr_setFirstUse {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getNumArguments! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_ValuePtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = ValuePtr.blockArgument arg then
      { arg.get! ctx with firstUse := newFirstUse }
    else
      arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_ValuePtr_setFirstUse {value : ValuePtr} :
    value.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = value then
      newFirstUse
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_ValuePtr_setFirstUse {value : ValuePtr} :
    value.getType! (ValuePtr.setFirstUse value' ctx newFirstUse h) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_ValuePtr_setFirstUse {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse value' then
      newFirstUse
    else
      opOperandPtr.get! ctx := by
  grind


