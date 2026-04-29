module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.allocEmpty -/

@[simp, grind =>]
theorem BlockPtr.get!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.get! ctx' = block.get! ctx := by
  grind

@[grind =>]
theorem OperationPtr.get!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.get! ctx' =
    if operation = op' then Operation.empty ty properties else operation.get! ctx := by
  grind

@[grind =>]
theorem OperationPtr.getNumResults!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNumResults! ctx' =
    if operation = op' then 0 else operation.getNumResults! ctx := by
  grind

@[grind =>]
theorem OpResultPtr.get!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.get! ctx' = opResult.get! ctx := by
  grind [Operation.default_results_eq]

@[grind =>]
theorem OperationPtr.getNumOperands!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNumOperands! ctx' =
    if operation = op' then 0 else operation.getNumOperands! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtr.get!_OperationPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.get! ctx' = opOperand.get! ctx := by
  grind [Operation.default_operands_eq]

@[simp, grind =>]
theorem OperationPtr.getProperties!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getProperties! ctx' ty =
    if operation = op' then properties else operation.getProperties! ctx ty := by
  grind

@[grind =>]
theorem OperationPtr.getOperands!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getOperands! ctx' =
    if operation = op' then #[] else operation.getOperands! ctx := by
  grind

@[grind =>]
theorem OperationPtr.getNumSuccessors!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNumSuccessors! ctx' =
    if operation = op' then 0 else operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =>]
theorem BlockOperandPtr.get!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.get! ctx' = blockOperand.get! ctx := by
  grind [Operation.default_blockOperands_eq]

@[grind =>]
theorem OperationPtr.getNumRegions!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNumRegions! ctx' =
    if operation = op' then 0 else operation.getNumRegions! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.getRegion!_OperationPtr_allocEmpty  {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getRegion! ctx' i = operation.getRegion! ctx i := by
  grind [Operation.default_regions_eq]

@[simp, grind =>]
theorem BlockOperandPtrPtr.get!_OperationPtr_allocEmpty {blockOperandPtr : BlockOperandPtrPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperandPtr.get! ctx' = blockOperandPtr.get! ctx := by
  grind

@[simp, grind =>]
theorem BlockPtr.getNumArguments!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.get!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind

@[simp, grind =>]
theorem RegionPtr.get!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.get! ctx' = region.get! ctx := by
  grind

@[simp, grind =>]
theorem ValuePtr.getFirstUse!_OperationPtr_allocEmpty {value : ValuePtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind

@[simp, grind =>]
theorem ValuePtr.getType!_OperationPtr_allocEmpty {value : ValuePtr}
    (h : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    value.getType! ctx' = value.getType! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtrPtr.get!_OperationPtr_allocEmpty {opOperandPtr : OpOperandPtrPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind

/- OperationPtr.dealloc -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_dealloc {block : BlockPtr} :
    block.get! (OperationPtr.dealloc operation' ctx hop') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.get! (OperationPtr.dealloc operation' ctx hop') =
    operation.get! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getProperties! (OperationPtr.dealloc operation' ctx hop') opCode =
    operation.getProperties! ctx opCode := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumResults! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opResult.get! (OperationPtr.dealloc operation' ctx hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumOperands! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperand.get! (OperationPtr.dealloc operation' ctx hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getOperands! (OperationPtr.dealloc operation' ctx hop') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumSuccessors! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    blockOperand.get! (OperationPtr.dealloc operation' ctx hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumRegions! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getRegion! (OperationPtr.dealloc operation' ctx hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_dealloc {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.InBounds (OperationPtr.dealloc operation' ctx hop') →
    blockOperandPtr.get! (OperationPtr.dealloc operation' ctx hop') =
    blockOperandPtr.get! ctx := by
  grind [BlockOperandPtr.InBounds]

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_dealloc {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.dealloc operation' ctx hop') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.dealloc operation' ctx hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_dealloc {region : RegionPtr} :
    region.get! (OperationPtr.dealloc operation' ctx hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_dealloc {value : ValuePtr} :
    value.InBounds (OperationPtr.dealloc operation' ctx hop') →
    value.getFirstUse! (OperationPtr.dealloc operation' ctx hop') =
    value.getFirstUse! ctx := by
  grind [OpResultPtr.InBounds]

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_dealloc {value : ValuePtr} :
    value.InBounds (OperationPtr.dealloc operation' ctx hop') →
    value.getType! (OperationPtr.dealloc operation' ctx hop') =
    value.getType! ctx := by
  grind [OpResultPtr.InBounds]

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_dealloc {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperandPtr.get! (OperationPtr.dealloc operation' ctx hop') =
    opOperandPtr.get! ctx := by
  grind [OpOperandPtr.InBounds]

