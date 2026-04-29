module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OpResultPtr.setType -/

@[simp, grind =]
theorem BlockPtr.get!_OpResultPtr_setType {block : BlockPtr} :
    block.get! (OpResultPtr.setType result' ctx newType hresult') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OpResultPtr_setType {operation : OperationPtr} :
    operation.get! (OpResultPtr.setType result' ctx newType hresult') =
    if result'.op = operation then
      {operation.get! ctx with results :=
        (operation.get! ctx).results.set! result'.index { result'.get! ctx with type := newType } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getProperties! (OpResultPtr.setType result' ctx newType hresult') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpResultPtr_setType {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setType result' ctx newType hresult')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpResultPtr_setType {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setType result' ctx newType hresult')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpResultPtr_setType {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setType result' ctx newType hresult')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpResultPtr_setType {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setType result' ctx newType hresult')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpResultPtr_setType {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setType result' ctx newType hresult')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_OpResultPtr_setType {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setType result' ctx newType hresult')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNumResults! (OpResultPtr.setType result' ctx hresult' newType) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.get! (OpResultPtr.setType result' ctx newType hresult') =
    if opResult = result' then
      { opResult.get! ctx with type := newType }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNumOperands! (OpResultPtr.setType result' ctx hresult' newType) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.get! (OpResultPtr.setType result' ctx newType hresult') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getOperands! (OpResultPtr.setType result' ctx hresult' newType) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNumSuccessors! (OpResultPtr.setType result' ctx hresult' newType) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpResultPtr.setType result' ctx newType hresult') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNumRegions! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getRegion! (OpResultPtr.setType result' ctx newType hresult') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpResultPtr_setType {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpResultPtr.setType result' ctx newType hresult') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpResultPtr_setType {block : BlockPtr} :
    block.getNumArguments! (OpResultPtr.setType result' ctx newType hresult') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpResultPtr_setType {arg : BlockArgumentPtr} :
    arg.get! (OpResultPtr.setType result' ctx newType hresult') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpResultPtr_setType {region : RegionPtr} :
    region.get! (OpResultPtr.setType result' ctx newType hresult') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OpResultPtr_setType {value : ValuePtr} :
    value.getFirstUse! (OpResultPtr.setType result' ctx newType hresult') =
    value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_OpResultPtr_setType {value : ValuePtr} :
    value.getType! (OpResultPtr.setType result' ctx newType hresult') =
    if value = result' then
      newType
    else
      value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OpResultPtr_setType {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpResultPtr.setType result' ctx newType hresult') =
    opOperandPtr.get! ctx := by
  grind


/- OpResultPtr.setFirstUse -/

@[simp, grind =]
theorem BlockPtr.get!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.get!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    if result'.op = operation then
      {operation.get! ctx with results :=
        (operation.get! ctx).results.set! result'.index { result'.get! ctx with firstUse := newFirstUse } }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getProperties! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult')).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_OpResultPtr_setFirstUse {operation : OperationPtr} :
    (operation.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumResults! (OpResultPtr.setFirstUse result' ctx hresult' newFirstUse) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    if opResult = result' then
      { opResult.get! ctx with firstUse := newFirstUse }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (OpResultPtr.setFirstUse result' ctx hresult' newFirstUse) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getOperands! (OpResultPtr.setFirstUse result' ctx hresult' newFirstUse) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumSuccessors! (OpResultPtr.setFirstUse result' ctx hresult' newFirstUse) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumRegions! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getRegion! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpResultPtr_setFirstUse {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getNumArguments! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpResultPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpResultPtr_setFirstUse {value : ValuePtr} :
    value.getFirstUse! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    if value = ValuePtr.opResult result' then
      newFirstUse
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpResultPtr_setFirstUse {value : ValuePtr} :
    value.getType! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpResultPtr_setFirstUse {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse (ValuePtr.opResult result') then
      newFirstUse
    else
      opOperandPtr.get! ctx := by
  grind

