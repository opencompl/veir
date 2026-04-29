module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.setResults -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setResults {block : BlockPtr} :
    block.get! (OperationPtr.setResults operation' ctx newResults hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setResults {operation : OperationPtr} :
    operation.get! (OperationPtr.setResults operation' ctx newResults hop') =
    if operation = operation' then
      { operation.get! ctx with results := newResults }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setResults operation' ctx newResults hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setResults {operation : OperationPtr} :
    (operation.get! (OperationPtr.setResults operation' ctx newResults hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setResults {operation : OperationPtr} :
    (operation.get! (OperationPtr.setResults operation' ctx newResults hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setResults {operation : OperationPtr} :
    (operation.get! (OperationPtr.setResults operation' ctx newResults hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_setResults {operation : OperationPtr} :
    (operation.get! (OperationPtr.setResults operation' ctx newResults hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setResults {operation : OperationPtr} :
    (operation.get! (OperationPtr.setResults operation' ctx newResults hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setResults operation' ctx newResults hop') =
    if operation = operation' then
      newResults.size
    else
      operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setResults operation' ctx newResults hop') =
    if opResult.op = operation' then
      newResults[opResult.index]!
    else
      opResult.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setResults {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setResults op ctx newResults hop) =
    opOperand.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getOperands!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setResults operation' ctx newResults hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setResults operation' ctx newResults hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setResults {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setResults operation' ctx newResults hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setResults {block : BlockPtr} {hop} :
    block.getNumArguments! (OperationPtr.setResults op ctx newResults hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setResults operation' ctx newResults hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setResults {region : RegionPtr} :
    region.get! (OperationPtr.setResults operation' ctx hop' newResults) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setResults {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setResults operation' ctx newResults hop') =
    match value with
    | .opResult result =>
      if result.op = operation' then
        newResults[result.index]!.firstUse
      else
        value.getFirstUse! ctx
    | _ =>
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_OperationPtr_setResults {value : ValuePtr} :
    value.getType! (OperationPtr.setResults operation' ctx newResults hop') =
    match value with
    | .opResult result =>
      if result.op = operation' then
        newResults[result.index]!.type
      else
        value.getType! ctx
    | _ =>
      value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setResults {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setResults op ctx newResults hop) =
    match opOperandPtr with
    | .valueFirstUse (.opResult result) =>
      if result.op = op then
        newResults[result.index]!.firstUse
      else
        opOperandPtr.get! ctx
    | _ =>
      opOperandPtr.get! ctx := by
  grind

/- OperationPtr.pushResult -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_pushResult {block : BlockPtr} :
    block.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    if operation = operation' then
      { operation.get! ctx with results := (operation.get! ctx).results.push newResult }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushResult operation' ctx newResult hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_pushResult {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushResult operation' ctx newResult hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_pushResult {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushResult operation' ctx newResult hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_pushResult {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushResult operation' ctx newResult hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OperationPtr_pushResult {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushResult operation' ctx newResult hop')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_pushResult {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushResult operation' ctx newResult hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[grind =]
theorem OperationPtr.getNumResults!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.pushResult operation' ctx newResult hop') =
    if operation = operation' then
      (operation.getNumResults! ctx) + 1
    else
      operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    if opResult = operation'.nextResult ctx then
      newResult
    else
      opResult.get! ctx := by
  grind [OperationPtr.getResult]

@[grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_pushResult {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.pushResult op ctx newResult hop) =
    opOperand.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getOperands!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.pushResult operation' ctx newResult hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_pushResult {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_pushResult {block : BlockPtr} {hop} :
    block.getNumArguments! (OperationPtr.pushResult op ctx newResult hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_pushResult {region : RegionPtr} :
    region.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_pushResult {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.pushResult operation' ctx newResult hop') =
    if value = ValuePtr.opResult (operation'.nextResult ctx) then
      newResult.firstUse
    else
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_OperationPtr_pushResult {value : ValuePtr} :
    value.getType! (OperationPtr.pushResult operation' ctx newResult hop') =
    if value = ValuePtr.opResult (operation'.nextResult ctx) then
      newResult.type
    else
      value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_pushResult {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.pushResult op ctx newResult hop) =
    if opOperandPtr = .valueFirstUse (ValuePtr.opResult (op.nextResult ctx)) then
      newResult.firstUse
    else
      opOperandPtr.get! ctx := by
  grind

