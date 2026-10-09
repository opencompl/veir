module

public import Veir.IR.Setters
import all Veir.IR.Basic
import all Veir.IR.Setters

namespace Veir

variable {OpInfo : Type} [IsOpCode OpInfo]
variable {ctx ctx': IRContext OpInfo}
variable {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]
variable {opCode opCode' : Dialect}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.allocEmpty -/

variable {CreateDialect : Type} [IsOpCode CreateDialect]
  [HasDialect OpInfo CreateDialect]
variable {ty : CreateDialect} {properties : propertiesOf ty}

@[simp, grind =>]
theorem BlockPtr.get!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.get! ctx' = block.get! ctx := by
  grind

@[simp, grind =>]
theorem BlockPtr.getParent!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getParent! ctx' =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getFirstUse!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getFirstUse! ctx' =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getFirstOp!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getFirstOp! ctx' =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getLastOp!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getLastOp! ctx' =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getNextBlock!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getNextBlock! ctx' =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getPrevBlock!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getPrevBlock! ctx' =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =>]
theorem OperationPtr.get!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.get! ctx' =
    if operation = op' then
      Operation.empty (ty : OpInfo) (HasDialect.ofDialectProperties OpInfo ty properties)
    else operation.get! ctx := by
  grind

@[grind =>]
theorem OperationPtr.getNextOp!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNextOp! ctx' =
    if operation = op' then none else operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[grind =>]
theorem OperationPtr.getPrevOp!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getPrevOp! ctx' =
    if operation = op' then none else operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[grind =>]
theorem OperationPtr.getParent!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getParent! ctx' =
    if operation = op' then none else operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[grind =>]
theorem OperationPtr.getAttributes!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getAttributes! ctx' =
    if operation = op' then DictionaryAttr.empty else operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[grind =>]
theorem OperationPtr.getOpType!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getOpType! ctx' =
    if operation = op' then (ty : OpInfo) else operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =>]
theorem OpResultPtr.getType!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =>]
theorem OpResultPtr.getFirstUse!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =>]
theorem OpResultPtr.getOwner!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

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
theorem OpOperandPtr.getNextUse!_OperationPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getBack!_OperationPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getOwner!_OperationPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getValue!_OperationPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getProperties!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getProperties! ctx' opCode =
    if operation = op' then
      if h : ofDialect OpInfo ty = ofDialect OpInfo opCode then
        HasDialect.properties_eq_of_ofDialect_eq h ▸ properties
      else default
    else
      operation.getProperties! ctx opCode := by
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

@[simp, grind =>]
theorem BlockOperandPtr.getNextUse!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getBack!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getOwner!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getValue!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

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
theorem BlockArgumentPtr.getType!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getIndex!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp]
theorem BlockArgumentPtr.getLoc!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (_heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getLoc! ctx' =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =>]
theorem BlockArgumentPtr.getOwner!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.get!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.get! ctx' = region.get! ctx := by
  grind

@[simp, grind =>]
theorem RegionPtr.getParent!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.getParent! ctx' =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.getFirstBlock!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.getFirstBlock! ctx' =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.getLastBlock!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.getLastBlock! ctx' =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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
theorem BlockPtr.getParent!_OperationPtr_dealloc {block : BlockPtr} :
    block.getParent! (OperationPtr.dealloc operation' ctx hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_dealloc {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.dealloc operation' ctx hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_dealloc {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.dealloc operation' ctx hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_dealloc {block : BlockPtr} :
    block.getLastOp! (OperationPtr.dealloc operation' ctx hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_dealloc {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.dealloc operation' ctx hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_dealloc {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.dealloc operation' ctx hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem OperationPtr.get!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.get! (OperationPtr.dealloc operation' ctx hop') =
    operation.get! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNextOp! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getPrevOp! (OperationPtr.dealloc operation' ctx hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getParent! (OperationPtr.dealloc operation' ctx hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getAttributes! (OperationPtr.dealloc operation' ctx hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getOpType! (OperationPtr.dealloc operation' ctx hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opResult.getIndex! (OperationPtr.dealloc operation' ctx hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opResult.getType! (OperationPtr.dealloc operation' ctx hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opResult.getFirstUse! (OperationPtr.dealloc operation' ctx hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opResult.getOwner! (OperationPtr.dealloc operation' ctx hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperand.getNextUse! (OperationPtr.dealloc operation' ctx hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperand.getBack! (OperationPtr.dealloc operation' ctx hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperand.getOwner! (OperationPtr.dealloc operation' ctx hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperand.getValue! (OperationPtr.dealloc operation' ctx hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    blockOperand.getNextUse! (OperationPtr.dealloc operation' ctx hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    blockOperand.getBack! (OperationPtr.dealloc operation' ctx hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    blockOperand.getOwner! (OperationPtr.dealloc operation' ctx hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc operation' ctx hop') →
    blockOperand.getValue! (OperationPtr.dealloc operation' ctx hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.dealloc operation' ctx hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.dealloc operation' ctx hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.dealloc operation' ctx hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.dealloc operation' ctx hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.dealloc operation' ctx hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_dealloc {region : RegionPtr} :
    region.get! (OperationPtr.dealloc operation' ctx hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_dealloc {region : RegionPtr} :
    region.getParent! (OperationPtr.dealloc operation' ctx hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_dealloc {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.dealloc operation' ctx hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_dealloc {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.dealloc operation' ctx hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- OperationPtr.setOperands -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setOperands {block : BlockPtr} :
    block.get! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setOperands {block : BlockPtr} :
    block.getParent! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setOperands {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setOperands {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setOperands {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setOperands {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setOperands {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    if operation = operation' then
      { operation.get! ctx with operands := newOperands }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setOperands operation' ctx newOperands hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setOperands operation' ctx newOperands hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setOperands operation' ctx newOperands hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setOperands operation' ctx newOperands hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setOperands operation' ctx newOperands hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setOperands operation' ctx newOperands hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setOperands operation' ctx newOperands hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setOperands operation' ctx newOperands hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setOperands operation' ctx newOperands hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setOperands operation' ctx newOperands hop') =
    if operation = operation' then
      newOperands.size
    else
      operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OperationPtr_setOperands {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setOperands op ctx newOperands hop) =
    if opOperand.op = op then
      newOperands[opOperand.index]!
    else
      opOperand.get! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setOperands {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setOperands op ctx newOperands hop) =
    if opOperand.op = op then newOperands[opOperand.index]!.nextUse else opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setOperands {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setOperands op ctx newOperands hop) =
    if opOperand.op = op then newOperands[opOperand.index]!.back else opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setOperands {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setOperands op ctx newOperands hop) =
    if opOperand.op = op then newOperands[opOperand.index]!.owner else opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setOperands {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setOperands op ctx newOperands hop) =
    if opOperand.op = op then newOperands[opOperand.index]!.value else opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[grind =]
theorem OperationPtr.getOperands!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setOperands operation' ctx newOperands hop') =
    if operation = operation' then
      newOperands.map (·.value)
    else
      operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setOperands {operation : OperationPtr} {hop} :
    operation.getNumRegions! (OperationPtr.setOperands op ctx newOperands hop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setOperands {operation : OperationPtr} {hop} :
    operation.getRegion! (OperationPtr.setOperands op ctx newOperands hop) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setOperands {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setOperands {block : BlockPtr} {hop} :
    block.getNumArguments! (OperationPtr.setOperands op ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setOperands operation' ctx newOperands hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setOperands {region : RegionPtr} :
    region.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setOperands {region : RegionPtr} :
    region.getParent! (OperationPtr.setOperands operation' ctx newOperands hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setOperands {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setOperands operation' ctx newOperands hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setOperands {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setOperands operation' ctx newOperands hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setOperands {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setOperands operation' ctx newOperands hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setOperands {value : ValuePtr} :
    value.getType! (OperationPtr.setOperands operation' ctx newOperands hop') =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setOperands {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setOperands op ctx newOperands hop) =
    match opOperandPtr with
    | .valueFirstUse _ =>
      opOperandPtr.get! ctx
    | .operandNextUse opOperand =>
      if opOperand.op = op then
        newOperands[opOperand.index]!.nextUse
      else
        (opOperand.get! ctx).nextUse := by
  grind

/- OperationPtr.pushOperand -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_pushOperand {block : BlockPtr} :
    block.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getParent! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    if operation = operation' then
      { operation.get! ctx with operands := (operation.get! ctx).operands.push newOperand }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushOperand operation' ctx newOperand hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_pushOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_pushOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_pushOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_pushOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.pushOperand operation' ctx hop' newOperands) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushOperand operation' ctx hop' newOperands) =
    if operation = operation' then
      (operation.getNumOperands! ctx) + 1
    else
      operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OperationPtr_pushOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.pushOperand op ctx newOperand hop) =
    if opOperand = op.nextOperand ctx then
      newOperand
    else
      opOperand.get! ctx := by
  grind [OperationPtr.getOpOperand]

@[grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushOperand op ctx newOperand hop) =
    if opOperand = op.nextOperand ctx then newOperand.nextUse
    else opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushOperand op ctx newOperand hop) =
    if opOperand = op.nextOperand ctx then newOperand.back
    else opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushOperand op ctx newOperand hop) =
    if opOperand = op.nextOperand ctx then newOperand.owner
    else opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushOperand op ctx newOperand hop) =
    if opOperand = op.nextOperand ctx then newOperand.value
    else opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[grind =]
theorem OperationPtr.getOperands!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.pushOperand operation' ctx hop' newOperands) =
    if operation = operation' then
      (operation.getOperands! ctx).push hop'.value
    else
      operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.pushOperand operation' ctx newOperand hop') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_pushOperand {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_pushOperand {block : BlockPtr} {hop} :
    block.getNumArguments! (OperationPtr.pushOperand op ctx newOperand hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_pushOperand {region : RegionPtr} :
    region.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushOperand {region : RegionPtr} :
    region.getParent! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushOperand {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushOperand {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_pushOperand {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_pushOperand {value : ValuePtr} :
    value.getType! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_pushOperand {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.pushOperand op ctx newOperand hop) =
    match opOperandPtr with
    | .valueFirstUse value =>
        value.getFirstUse! (OperationPtr.pushOperand op ctx newOperand hop)
    | .operandNextUse opOperand =>
      if opOperand = op.nextOperand ctx then
        newOperand.nextUse
      else
        (opOperand.get! ctx).nextUse := by
  grind

/- OperationPtr.setBlockOperands -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.get! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getParent! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setBlockOperands operation' ctx hop' newOperands) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if operation = operation' then
      {operation.get! ctx with blockOperands := newOperands}
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setBlockOperands operation' ctx newOperands hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getOperands! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if operation = operation' then
      newOperands.size
    else
      operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if blockOperand.op = operation' then
      newOperands[blockOperand.index]!
    else
      blockOperand.get! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if blockOperand.op = operation' then newOperands[blockOperand.index]!.nextUse else blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if blockOperand.op = operation' then newOperands[blockOperand.index]!.back else blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if blockOperand.op = operation' then newOperands[blockOperand.index]!.owner else blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if blockOperand.op = operation' then newOperands[blockOperand.index]!.value else blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setBlockOperands op ctx newOperands hop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setBlockOperands op ctx newOperands hop) i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setBlockOperands {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    match blockOperandPtr with
    | .blockOperandNextUse blockOperand =>
      if blockOperand.op = operation' then
        newOperands[blockOperand.index]!.nextUse
      else
        blockOperandPtr.get! ctx
    | .blockFirstUse _ =>
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setBlockOperands op ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.getParent! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setBlockOperands {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setBlockOperands {value : ValuePtr} :
    value.getType! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setBlockOperands {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setBlockOperands op ctx newOperands hop) =
    opOperandPtr.get! ctx := by
  grind

/- OperationPtr.pushBlockOperand -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getParent! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if operation = operation' then
      {operation.get! ctx with blockOperands := (operation.get! ctx).blockOperands.push newOperand}
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.pushBlockOperand operation' ctx hop' newOperands) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushBlockOperand operation' ctx hop' newOperands) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_pushBlockOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushBlockOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushBlockOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushBlockOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushBlockOperand {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.pushBlockOperand operation' ctx hop' newOperands) =
    operation.getOperands! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if operation = operation' then
      (operation.getNumSuccessors! ctx) + 1
    else
      operation.getNumSuccessors! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperand = operation'.nextBlockOperand ctx then
      newOperand
    else
      blockOperand.get! ctx := by
  grind [OperationPtr.getBlockOperand]

@[grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperand = operation'.nextBlockOperand ctx then
      newOperand.nextUse
    else blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperand = operation'.nextBlockOperand ctx then
      newOperand.back
    else blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperand = operation'.nextBlockOperand ctx then
      newOperand.owner
    else blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperand = operation'.nextBlockOperand ctx then
      newOperand.value
    else blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_pushBlockOperand {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperandPtr = .blockOperandNextUse (operation'.nextBlockOperand ctx) then
      newOperand.nextUse
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.getParent! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_pushBlockOperand {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_pushBlockOperand {value : ValuePtr} :
    value.getType! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_pushBlockOperand {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    opOperandPtr.get! ctx := by
  grind

/- OperationPtr.setResults -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setResults {block : BlockPtr} :
    block.get! (OperationPtr.setResults operation' ctx newResults hop') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setResults {block : BlockPtr} :
    block.getParent! (OperationPtr.setResults operation' ctx newResults hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setResults {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setResults operation' ctx newResults hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setResults {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setResults operation' ctx newResults hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setResults {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setResults operation' ctx newResults hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setResults {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setResults operation' ctx newResults hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setResults {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setResults operation' ctx newResults hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setResults operation' ctx newResults hop') =
    if opResult.op = operation' then newResults[opResult.index]!.index else opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem OpResultPtr.getType!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setResults operation' ctx newResults hop') =
    if opResult.op = operation' then newResults[opResult.index]!.type else opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setResults operation' ctx newResults hop') =
    if opResult.op = operation' then newResults[opResult.index]!.firstUse else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setResults operation' ctx newResults hop') =
    if opResult.op = operation' then newResults[opResult.index]!.owner else opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setResults {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setResults op ctx newResults hop) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setResults {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setResults op ctx newResults hop) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setResults {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setResults op ctx newResults hop) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setResults {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setResults op ctx newResults hop) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setResults operation' ctx newResults hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setResults operation' ctx newResults hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setResults operation' ctx newResults hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setResults operation' ctx newResults hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setResults operation' ctx newResults hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setResults operation' ctx newResults hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setResults operation' ctx newResults hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setResults operation' ctx newResults hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setResults operation' ctx newResults hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setResults {region : RegionPtr} :
    region.get! (OperationPtr.setResults operation' ctx hop' newResults) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setResults {region : RegionPtr} :
    region.getParent! (OperationPtr.setResults operation' ctx hop' newResults) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setResults {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setResults operation' ctx hop' newResults) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setResults {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setResults operation' ctx hop' newResults) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushResult {block : BlockPtr} :
    block.getParent! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushResult {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushResult {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushResult {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushResult {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushResult {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushResult operation' ctx newResult hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushResult operation' ctx newResult hop') =
    if opResult = operation'.nextResult ctx then newResult.index
    else opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem OpResultPtr.getType!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushResult operation' ctx newResult hop') =
    if opResult = operation'.nextResult ctx then newResult.type
    else opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushResult operation' ctx newResult hop') =
    if opResult = operation'.nextResult ctx then newResult.firstUse
    else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushResult operation' ctx newResult hop') =
    if opResult = operation'.nextResult ctx then newResult.owner
    else opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

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

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushResult {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushResult op ctx newResult hop) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushResult {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushResult op ctx newResult hop) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushResult {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushResult op ctx newResult hop) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushResult {op : OperationPtr} {hop} {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushResult op ctx newResult hop) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushResult operation' ctx newResult hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_pushResult {region : RegionPtr} :
    region.get! (OperationPtr.pushResult operation' ctx newResult hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushResult {region : RegionPtr} :
    region.getParent! (OperationPtr.pushResult operation' ctx newResult hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushResult {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushResult operation' ctx newResult hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushResult {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushResult operation' ctx newResult hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- OperationPtr.setProperties -/

section OperationPtr.setProperties

variable {operation' : OperationPtr}
variable {newProperties : propertiesOf opCode}
variable {inBounds : operation'.InBounds ctx}
variable {hprop : operation'.getOpType! ctx = opCode}

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setProperties {block : BlockPtr} :
    block.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setProperties {block : BlockPtr} :
    block.getParent! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setProperties {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setProperties {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setProperties {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setProperties {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setProperties {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    if operation = operation' then
      { operation.get! ctx with
        opType := operation'.getOpType! ctx
        properties := hprop ▸ HasDialect.ofDialectProperties OpInfo opCode newProperties }
    else
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[grind =]
theorem OperationPtr.getProperties!_OperationPtr_setProperties
    {GetterDialect : Type} [IsOpCode GetterDialect]
    [HasDialect OpInfo GetterDialect] {getterOpCode : GetterDialect}
    {operation : OperationPtr} :
    operation.getProperties!
      (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop)
      getterOpCode =
    if operation = operation' then
      if h : ofDialect OpInfo opCode = ofDialect OpInfo getterOpCode then
        HasDialect.properties_eq_of_ofDialect_eq h ▸ newProperties
      else
        default
    else
      operation.getProperties! ctx getterOpCode := by
  grind

/- We probably do not want both this lemma and the previous one to be grind.
  TODO: make a decision about this
-/
@[grind =]
theorem OperationPtr.getProperties!_OperationPtr_setProperties_same_opCode {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) opCode =
    if operation = operation' then
      newProperties
    else
      operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OperationPtr_setProperties {operation : OperationPtr} :
    (operation.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getOperands! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumRegions! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getRegion! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_setProperties {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_setProperties {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setProperties {region : RegionPtr} :
    region.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setProperties {region : RegionPtr} :
    region.getParent! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setProperties {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setProperties {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_setProperties {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_setProperties {value : ValuePtr} :
    value.getType! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_setProperties {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    opOperandPtr.get! ctx := by
  grind

end OperationPtr.setProperties

/- OperationPtr.setAttributes -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setAttributes {block : BlockPtr} :
    block.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getParent! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    if operation = operation' then newAttrs else operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setAttributes {region : RegionPtr} :
    region.get! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setAttributes {region : RegionPtr} :
    region.getParent! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setAttributes {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setAttributes {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- OperationPtr.setRegions -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setRegions {block : BlockPtr} :
    block.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setRegions {block : BlockPtr} :
    block.getParent! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setRegions {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setRegions {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setRegions {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setRegions {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setRegions {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setRegions operation' ctx newRegions hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setRegions {region : RegionPtr} :
    region.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setRegions {region : RegionPtr} :
    region.getParent! (OperationPtr.setRegions operation' ctx newRegions hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setRegions {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setRegions operation' ctx newRegions hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setRegions {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setRegions operation' ctx newRegions hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getParent! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_pushRegion {region : RegionPtr} :
    region.get! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushRegion {region : RegionPtr} :
    region.getParent! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushRegion {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushRegion {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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


/- BlockArgumentPtr.setType -/

@[grind =]
theorem BlockPtr.get!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    if arg'.block = block then
      { block.get! ctx with arguments := (block.get! ctx).arguments.set! arg'.index { arg'.get! ctx with type := newType } }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setType arg' ctx newType harg') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setType arg' ctx newType harg') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setType arg' ctx newType harg') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setType arg' ctx newType harg') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setType arg' ctx newType harg') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setType arg' ctx newType harg') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockArgumentPtr_setType {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setType arg' ctx newType harg')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockArgumentPtr_setType {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setType arg' ctx newType harg')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockArgumentPtr_setType {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setType arg' ctx newType harg')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockArgumentPtr_setType {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setType arg' ctx newType harg')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockArgumentPtr_setType {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setType arg' ctx newType harg')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockArgumentPtr_setType {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setType arg' ctx newType harg')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getOpType! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getProperties! (BlockArgumentPtr.setType arg' ctx newType harg') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNumResults! (BlockArgumentPtr.setType arg' ctx harg' newType) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getIndex! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNumOperands! (BlockArgumentPtr.setType arg' ctx harg' newType) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getOperands! (BlockArgumentPtr.setType arg' ctx harg' newType) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setType arg' ctx newType harg') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setType arg' ctx newType harg') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setType arg' ctx newType harg') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setType arg' ctx newType harg') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNumRegions! (BlockArgumentPtr.setType arg' ctx newType harg') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getRegion! (BlockArgumentPtr.setType arg' ctx newType harg') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockArgumentPtr_setType {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockArgumentPtr_setType {block : BlockPtr} {hop} :
    block.getNumArguments! (BlockArgumentPtr.setType op ctx newType hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_BlockArgumentPtr_setType {arg : BlockArgumentPtr} :
    arg.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    if arg = arg' then
      { arg.get! ctx with type := newType }
    else
      arg.get! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setType {arg : BlockArgumentPtr} :
    arg.getType! (BlockArgumentPtr.setType arg' ctx newType harg') =
    if arg = arg' then newType else arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setType {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockArgumentPtr.setType arg' ctx newType harg') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setType {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockArgumentPtr.setType arg' ctx newType harg') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setType {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockArgumentPtr.setType arg' ctx newType harg') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setType {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockArgumentPtr.setType arg' ctx newType harg') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setType arg' ctx newType harg') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setType arg' ctx newType harg') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setType arg' ctx newType harg') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockArgumentPtr_setType {value : ValuePtr} :
    value.getFirstUse! (BlockArgumentPtr.setType arg' ctx newType harg') =
    value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_BlockArgumentPtr_setType {value : ValuePtr} :
    value.getType! (BlockArgumentPtr.setType arg' ctx newType harg') =
    if arg' = value then
      newType
    else
      value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockArgumentPtr_setType {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    opOperandPtr.get! ctx := by
  grind

/- BlockArgumentPtr.setFirstUse -/

@[grind =]
theorem BlockPtr.get!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    if arg'.block = block then
      { block.get! ctx with arguments := (block.get! ctx).arguments.set! arg'.index { arg'.get! ctx with firstUse := newFirstUse } }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getOpType! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getProperties! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumResults! (BlockArgumentPtr.setFirstUse arg' ctx harg' newFirstUse) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (BlockArgumentPtr.setFirstUse arg' ctx harg' newFirstUse) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getOperands! (BlockArgumentPtr.setFirstUse arg' ctx harg' newFirstUse) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumRegions! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getRegion! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockArgumentPtr_setFirstUse {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockArgumentPtr_setFirstUse {block : BlockPtr} {hop} :
    block.getNumArguments! (BlockArgumentPtr.setFirstUse op ctx newFirstUse hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_BlockArgumentPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    if arg = arg' then
      { arg.get! ctx with firstUse := newFirstUse }
    else
      arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getType! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    if arg = arg' then newFirstUse else arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_BlockArgumentPtr_setFirstUse {value : ValuePtr} :
    value.getFirstUse! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    if value = ValuePtr.blockArgument arg' then
      newFirstUse
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockArgumentPtr_setFirstUse {value : ValuePtr} :
    value.getType! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_BlockArgumentPtr_setFirstUse {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse (ValuePtr.blockArgument arg') then
      newFirstUse
    else
      opOperandPtr.get! ctx := by
  grind

/- BlockArgumentPtr.setLoc -/

@[grind =]
theorem BlockPtr.get!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    if arg'.block = block then
      { block.get! ctx with arguments := (block.get! ctx).arguments.set! arg'.index { arg'.get! ctx with loc := newLoc } }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    (block.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getOpType! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getProperties! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNumResults! (BlockArgumentPtr.setLoc arg' ctx harg' newLoc) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getIndex! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNumOperands! (BlockArgumentPtr.setLoc arg' ctx harg' newLoc) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getOperands! (BlockArgumentPtr.setLoc arg' ctx harg' newLoc) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNumRegions! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getRegion! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockArgumentPtr_setLoc {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockArgumentPtr_setLoc {block : BlockPtr} {hop} :
    block.getNumArguments! (BlockArgumentPtr.setLoc op ctx newLoc hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_BlockArgumentPtr_setLoc {arg : BlockArgumentPtr} :
    arg.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    if arg = arg' then
      { arg.get! ctx with loc := newLoc }
    else
      arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setLoc {arg : BlockArgumentPtr} :
    arg.getType! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setLoc {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setLoc {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setLoc {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    if arg = arg' then newLoc else arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setLoc {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockArgumentPtr_setLoc {value : ValuePtr} :
    value.getFirstUse! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockArgumentPtr_setLoc {value : ValuePtr} :
    value.getType! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockArgumentPtr_setLoc {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    opOperandPtr.get! ctx := by
  grind

/- BlockPtr.allocEmpty -/

@[grind =>]
theorem BlockPtr.get!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.get! ctx' = if block = bl' then Block.empty else block.get! ctx := by
  grind

@[grind =>]
theorem BlockPtr.getParent!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getParent! ctx' =
    if block = bl' then none else block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[grind =>]
theorem BlockPtr.getFirstUse!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getFirstUse! ctx' =
    if block = bl' then none else block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[grind =>]
theorem BlockPtr.getFirstOp!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getFirstOp! ctx' =
    if block = bl' then none else block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[grind =>]
theorem BlockPtr.getLastOp!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getLastOp! ctx' =
    if block = bl' then none else block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[grind =>]
theorem BlockPtr.getNextBlock!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getNextBlock! ctx' =
    if block = bl' then none else block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[grind =>]
theorem BlockPtr.getPrevBlock!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getPrevBlock! ctx' =
    if block = bl' then none else block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.get!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.get! ctx' = operation.get! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.getNextOp!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getNextOp! ctx' =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getPrevOp!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getPrevOp! ctx' =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getParent!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getParent! ctx' =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getAttributes!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getAttributes! ctx' =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getOpType!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getOpType! ctx' = operation.getOpType! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.getProperties!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getProperties! ctx' opCode = operation.getProperties! ctx opCode := by
  grind

@[simp, grind =>]
theorem OperationPtr.getNumResults!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getNumResults! ctx' = operation.getNumResults! ctx := by
  grind

@[simp, grind =>]
theorem OpResultPtr.get!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opResult.get! ctx' = opResult.get! ctx := by
  grind

@[simp, grind =>]
theorem OpResultPtr.getIndex!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =>]
theorem OpResultPtr.getType!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =>]
theorem OpResultPtr.getFirstUse!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =>]
theorem OpResultPtr.getOwner!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getNumOperands!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtr.get!_BlockPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperand.get! ctx' = opOperand.get! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtr.getNextUse!_BlockPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getBack!_BlockPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getOwner!_BlockPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getValue!_BlockPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getOperands!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getOperands! ctx' = operation.getOperands! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.getNumSuccessors!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getNumSuccessors! ctx' = operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =>]
theorem BlockOperandPtr.get!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockOperand.get! ctx' = blockOperand.get! ctx := by
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getNextUse!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getBack!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getOwner!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getValue!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getNumRegions!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    operation.getNumRegions! ctx' = operation.getNumRegions! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.getRegion!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    operation.getRegion! ctx' i = operation.getRegion! ctx i := by
  grind

@[simp, grind =>]
theorem BlockPtr.getNumArguments!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    block.getNumArguments! ctx' =
    if block = bl' then 0 else block.getNumArguments! ctx := by
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.get!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind [Block.default_arguments_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getType!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getIndex!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp]
theorem BlockArgumentPtr.getLoc!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (_heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockArg.getLoc! ctx' =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =>]
theorem BlockArgumentPtr.getOwner!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.get!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    region.get! ctx' = region.get! ctx := by
  grind

@[simp, grind =>]
theorem RegionPtr.getParent!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    region.getParent! ctx' =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.getFirstBlock!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    region.getFirstBlock! ctx' =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.getLastBlock!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    region.getLastBlock! ctx' =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =>]
theorem ValuePtr.getFirstUse!_BlockPtr_allocEmpty {value : ValuePtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind

 @[simp, grind =>]
theorem ValuePtr.getType!_BlockPtr_allocEmpty {value : ValuePtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    value.getType! ctx' = value.getType! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtrPtr.get!_BlockPtr_allocEmpty {opOperandPtr : OpOperandPtrPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind

/- BlockPtr.dealloc -/

@[simp, grind =]
theorem BlockPtr.get!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.get! (BlockPtr.dealloc block' ctx hblock') =
    block.get! ctx := by
  grind [BlockPtr.InBounds]

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getParent! (BlockPtr.dealloc block' ctx hblock') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getFirstUse! (BlockPtr.dealloc block' ctx hblock') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getFirstOp! (BlockPtr.dealloc block' ctx hblock') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getLastOp! (BlockPtr.dealloc block' ctx hblock') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getNextBlock! (BlockPtr.dealloc block' ctx hblock') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getPrevBlock! (BlockPtr.dealloc block' ctx hblock') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.get! (BlockPtr.dealloc block' ctx hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.dealloc block' ctx hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.dealloc block' ctx hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getParent! (BlockPtr.dealloc block' ctx hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.dealloc block' ctx hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.dealloc block' ctx hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.dealloc block' ctx hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.dealloc block' ctx hblock') =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_dealloc {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.dealloc block' ctx hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_dealloc {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.dealloc block' ctx hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_dealloc {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.dealloc block' ctx hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_dealloc {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.dealloc block' ctx hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_dealloc {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.dealloc block' ctx hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.dealloc block' ctx hblock') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.dealloc block' ctx hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.dealloc block' ctx hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.dealloc block' ctx hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.dealloc block' ctx hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.dealloc block' ctx hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.dealloc block' ctx hblock') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.dealloc block' ctx hblock') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.dealloc block' ctx hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.dealloc block' ctx hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.dealloc block' ctx hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.dealloc block' ctx hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.dealloc block' ctx hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.dealloc block' ctx hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_dealloc {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.dealloc block' ctx hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_dealloc {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockOperandPtr.get! (BlockPtr.dealloc block' ctx hblock') =
    blockOperandPtr.get! ctx := by
  grind [BlockPtr.InBounds]

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_dealloc {block : BlockPtr} :
    block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    block.getNumArguments! (BlockPtr.dealloc block' ctx hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockArg.get! (BlockPtr.dealloc block' ctx hblock') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockArg.getType! (BlockPtr.dealloc block' ctx hblock') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockArg.getFirstUse! (BlockPtr.dealloc block' ctx hblock') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockArg.getIndex! (BlockPtr.dealloc block' ctx hblock') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockArg.getLoc! (BlockPtr.dealloc block' ctx hblock') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.block.InBounds (BlockPtr.dealloc block' ctx hblock') →
    blockArg.getOwner! (BlockPtr.dealloc block' ctx hblock') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_dealloc {region : RegionPtr} :
    region.get! (BlockPtr.dealloc block' ctx hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_dealloc {region : RegionPtr} :
    region.getParent! (BlockPtr.dealloc block' ctx hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_dealloc {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.dealloc block' ctx hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_dealloc {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.dealloc block' ctx hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_dealloc {value : ValuePtr} :
    value.InBounds (BlockPtr.dealloc block' ctx hblock') →
    value.getFirstUse! (BlockPtr.dealloc block' ctx hblock') =
    value.getFirstUse! ctx := by
  grind [BlockArgumentPtr.InBounds]

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_dealloc {value : ValuePtr} :
    value.InBounds (BlockPtr.dealloc block' ctx hblock') →
    value.getType! (BlockPtr.dealloc block' ctx hblock') =
    value.getType! ctx := by
  grind [BlockArgumentPtr.InBounds]

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_dealloc {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.InBounds (BlockPtr.dealloc block' ctx hblock') →
    opOperandPtr.get! (BlockPtr.dealloc block' ctx hblock') =
    opOperandPtr.get! ctx := by
  grind [BlockArgumentPtr.InBounds]

/- BlockPtr.setParent -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setParent {block : BlockPtr} :
    block.get! (BlockPtr.setParent block' ctx newParent hblock') =
    if block' = block then
      { block.get! ctx with parent := newParent }
    else
      block.get! ctx := by
  grind

@[grind =]
theorem BlockPtr.getParent!_BlockPtr_setParent {block : BlockPtr} :
    block.getParent! (BlockPtr.setParent block' ctx newParent hblock') =
    if block' = block then newParent else block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setParent {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setParent {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setParent {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setParent {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setParent {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_setParent {block : BlockPtr} :
    (block.get! (BlockPtr.setParent block' ctx newParent hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_setParent {block : BlockPtr} :
    (block.get! (BlockPtr.setParent block' ctx newParent hblock')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_setParent {block : BlockPtr} :
    (block.get! (BlockPtr.setParent block' ctx newParent hblock')).next =
    (block.get! ctx).next := by
  grind

@[grind =]
theorem BlockPtr.parent!_BlockPtr_setParent {block : BlockPtr} :
    (block.get! (BlockPtr.setParent block' ctx newParent hblock')).parent =
    if block' = block then
      newParent
    else
      (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_setParent {block : BlockPtr} :
    (block.get! (BlockPtr.setParent block' ctx newParent hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_setParent {block : BlockPtr} :
    (block.get! (BlockPtr.setParent block' ctx newParent hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setParent {operation : OperationPtr} :
    operation.get! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setParent block' ctx newParent hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setParent block' ctx hblock' newParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setParent block' ctx hblock' newParent) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setParent block' ctx hblock' newParent) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setParent block' ctx hblock' newParent) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.setParent block' ctx newParent hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setParent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setParent {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setParent {arg : BlockArgumentPtr} :
    arg.get! (BlockPtr.setParent block' ctx newParent hblock') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setParent {arg : BlockArgumentPtr} :
    arg.getType! (BlockPtr.setParent block' ctx newParent hblock') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setParent {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setParent {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockPtr.setParent block' ctx newParent hblock') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setParent {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockPtr.setParent block' ctx newParent hblock') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setParent {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setParent {region : RegionPtr} :
    region.get! (BlockPtr.setParent block' ctx newParent hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setParent {region : RegionPtr} :
    region.getParent! (BlockPtr.setParent block' ctx newParent hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setParent {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setParent {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setParent {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_setParent {value : ValuePtr} :
    value.getType! (BlockPtr.setParent block' ctx newParent hblock') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setParent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperandPtr.get! ctx := by
  grind


/- BlockPtr.setFirstUse -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    if block' = block then
      { block.get! ctx with firstUse := newFirstUse }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getParent! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    if block' = block then newFirstUse else block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem BlockPtr.firstUse!_BlockPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock')).firstUse =
    if block' = block then
      newFirstUse
    else
      (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstUse block' ctx hblock' newFirstUse)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_setFirstUse {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setFirstUse block' ctx hblock' newFirstUse) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setFirstUse block' ctx hblock' newFirstUse) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setFirstUse block' ctx hblock' newFirstUse) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setFirstUse block' ctx hblock' newFirstUse) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setFirstUse {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    if blockOperandPtr = BlockOperandPtrPtr.blockFirstUse block' then
      newFirstUse
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getType! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.getParent! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setFirstUse {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_setFirstUse {value : ValuePtr} :
    value.getType! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setFirstUse {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperandPtr.get! ctx := by
  grind


/- BlockPtr.setFirstOp -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    if block' = block then
      { block.get! ctx with firstOp := newFirstOp }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getParent! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    if block' = block then newFirstOp else block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_setFirstOp {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_setFirstOp {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_setFirstOp {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_setFirstOp {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[grind =]
theorem BlockPtr.firstOp!_BlockPtr_setFirstOp {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock')).firstOp =
    if block' = block then
      newFirstOp
    else
      (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_setFirstOp {block : BlockPtr} :
    (block.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setFirstOp block' ctx hblock' newFirstOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setFirstOp block' ctx hblock' newFirstOp) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setFirstOp block' ctx hblock' newFirstOp) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setFirstOp block' ctx hblock' newFirstOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setFirstOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setFirstOp {arg : BlockArgumentPtr} :
    arg.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setFirstOp {arg : BlockArgumentPtr} :
    arg.getType! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setFirstOp {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setFirstOp {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setFirstOp {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setFirstOp {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.getParent! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setFirstOp {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_setFirstOp {value : ValuePtr} :
    value.getType! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setFirstOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperandPtr.get! ctx := by
  grind


/- BlockPtr.setLastOp -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setLastOp {block : BlockPtr} :
    block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    if block' = block then
      { block.get! ctx with lastOp := newLastOp }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getParent! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    if block' = block then newLastOp else block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_setLastOp {block : BlockPtr} :
    (block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_setLastOp {block : BlockPtr} :
    (block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_setLastOp {block : BlockPtr} :
    (block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_setLastOp {block : BlockPtr} :
    (block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_setLastOp {block : BlockPtr} :
    (block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[grind =]
theorem BlockPtr.lastOp!_BlockPtr_setLastOp {block : BlockPtr} :
    (block.get! (BlockPtr.setLastOp block' ctx newLastOp hblock')).lastOp =
    if block' = block then
      newLastOp
    else
      (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setLastOp block' ctx newLastOp hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setLastOp block' ctx hblock' newLastOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setLastOp block' ctx hblock' newLastOp) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setLastOp block' ctx hblock' newLastOp) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setLastOp block' ctx hblock' newLastOp) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.setLastOp block' ctx newLastOp hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setLastOp {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setLastOp {arg : BlockArgumentPtr} :
    arg.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setLastOp {arg : BlockArgumentPtr} :
    arg.getType! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setLastOp {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setLastOp {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setLastOp {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setLastOp {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setLastOp {region : RegionPtr} :
    region.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setLastOp {region : RegionPtr} :
    region.getParent! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setLastOp {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setLastOp {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setLastOp {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_setLastOp {value : ValuePtr} :
    value.getType! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setLastOp {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperandPtr.get! ctx := by
  grind

/- BlockPtr.setNextBlock -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    if block' = block then
      { block.get! ctx with next := newNextBlock }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getParent! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    if block' = block then newNextBlock else block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_setNextBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_setNextBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock')).prev =
    (block.get! ctx).prev := by
  grind

@[grind =]
theorem BlockPtr.next!_BlockPtr_setNextBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock')).next =
    if block' = block then
      newNextBlock
    else
      (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_setNextBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_setNextBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_setNextBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setNextBlock block' ctx hblock' newNextBlock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setNextBlock block' ctx hblock' newNextBlock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setNextBlock block' ctx hblock' newNextBlock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setNextBlock block' ctx hblock' newNextBlock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setNextBlock {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setNextBlock {arg : BlockArgumentPtr} :
    arg.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setNextBlock {arg : BlockArgumentPtr} :
    arg.getType! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setNextBlock {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setNextBlock {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setNextBlock {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setNextBlock {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.getParent! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setNextBlock {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_setNextBlock {value : ValuePtr} :
    value.getType! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setNextBlock {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    opOperandPtr.get! ctx := by
  grind


/- BlockPtr.setPrevBlock -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    if block' = block then
      { block.get! ctx with prev := newPrevBlock }
    else
      block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getParent! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    if block' = block then newPrevBlock else block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_setPrevBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[grind =]
theorem BlockPtr.prev!_BlockPtr_setPrevBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock')).prev =
    if block' = block then
      newPrevBlock
    else
      (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_setPrevBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_setPrevBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_setPrevBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_setPrevBlock {block : BlockPtr} :
    (block.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setPrevBlock block' ctx hblock' newPrevBlock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setPrevBlock block' ctx hblock' newPrevBlock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setPrevBlock block' ctx hblock' newPrevBlock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setPrevBlock block' ctx hblock' newPrevBlock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setPrevBlock {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setPrevBlock {arg : BlockArgumentPtr} :
    arg.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setPrevBlock {arg : BlockArgumentPtr} :
    arg.getType! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setPrevBlock {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setPrevBlock {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setPrevBlock {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setPrevBlock {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.getParent! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setPrevBlock {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockPtr_setPrevBlock {value : ValuePtr} :
    value.getType! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setPrevBlock {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    opOperandPtr.get! ctx := by
  grind


/- OpOperandPtr.setNextUse -/

@[simp, grind =]
theorem BlockPtr.get!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if opOperand = operand' then newNextUse else opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OpOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getType! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getIndex! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getLoc! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getOwner! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.get! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    if opOperand = operand' then newBack else opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

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
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OpOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getType! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getIndex! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getLoc! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getOwner! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setBack {region : RegionPtr} :
    region.get! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setBack {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setBack {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setBack {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    if opOperand = operand' then newOwner else opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

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
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OpOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getType! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getIndex! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getLoc! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getOwner! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.get! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    if opOperand = operand' then newValue else opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

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
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OpOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getType! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getIndex! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getLoc! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getOwner! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_setValue {region : RegionPtr} :
    region.get! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setValue {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setValue {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setValue {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- OpResultPtr.setType -/

@[simp, grind =]
theorem BlockPtr.get!_OpResultPtr_setType {block : BlockPtr} :
    block.get! (OpResultPtr.setType result' ctx newType hresult') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpResultPtr_setType {block : BlockPtr} :
    block.getParent! (OpResultPtr.setType result' ctx newType hresult') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpResultPtr_setType {block : BlockPtr} :
    block.getFirstUse! (OpResultPtr.setType result' ctx newType hresult') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpResultPtr_setType {block : BlockPtr} :
    block.getFirstOp! (OpResultPtr.setType result' ctx newType hresult') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpResultPtr_setType {block : BlockPtr} :
    block.getLastOp! (OpResultPtr.setType result' ctx newType hresult') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpResultPtr_setType {block : BlockPtr} :
    block.getNextBlock! (OpResultPtr.setType result' ctx newType hresult') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpResultPtr_setType {block : BlockPtr} :
    block.getPrevBlock! (OpResultPtr.setType result' ctx newType hresult') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNextOp! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getPrevOp! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getParent! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getAttributes! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getOpType! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getIndex! (OpResultPtr.setType result' ctx newType hresult') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem OpResultPtr.getType!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getType! (OpResultPtr.setType result' ctx newType hresult') =
    if opResult = result' then newType else opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpResultPtr.setType result' ctx newType hresult') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getOwner! (OpResultPtr.setType result' ctx newType hresult') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpResultPtr.setType result' ctx newType hresult') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpResultPtr.setType result' ctx newType hresult') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpResultPtr.setType result' ctx newType hresult') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpResultPtr.setType result' ctx newType hresult') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpResultPtr.setType result' ctx newType hresult') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpResultPtr.setType result' ctx newType hresult') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpResultPtr.setType result' ctx newType hresult') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpResultPtr.setType result' ctx newType hresult') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OpResultPtr_setType {arg : BlockArgumentPtr} :
    arg.getType! (OpResultPtr.setType result' ctx newType hresult') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpResultPtr_setType {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpResultPtr.setType result' ctx newType hresult') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpResultPtr_setType {arg : BlockArgumentPtr} :
    arg.getIndex! (OpResultPtr.setType result' ctx newType hresult') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpResultPtr_setType {arg : BlockArgumentPtr} :
    arg.getLoc! (OpResultPtr.setType result' ctx newType hresult') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpResultPtr_setType {arg : BlockArgumentPtr} :
    arg.getOwner! (OpResultPtr.setType result' ctx newType hresult') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpResultPtr_setType {region : RegionPtr} :
    region.get! (OpResultPtr.setType result' ctx newType hresult') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpResultPtr_setType {region : RegionPtr} :
    region.getParent! (OpResultPtr.setType result' ctx newType hresult') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpResultPtr_setType {region : RegionPtr} :
    region.getFirstBlock! (OpResultPtr.setType result' ctx newType hresult') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpResultPtr_setType {region : RegionPtr} :
    region.getLastBlock! (OpResultPtr.setType result' ctx newType hresult') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getParent! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getOpType! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    if opResult = result' then newFirstUse else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OpResultPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getType! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpResultPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpResultPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getIndex! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpResultPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getLoc! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpResultPtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getOwner! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.get! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.getParent! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- OperationPtr.allocEmpty -/

@[simp, grind =>]
theorem BlockPtr.get!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.get! ctx' = block.get! ctx := by
  grind

@[simp, grind =>]
theorem BlockPtr.getParent!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getParent! ctx' =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getFirstUse!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getFirstUse! ctx' =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getFirstOp!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getFirstOp! ctx' =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getLastOp!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getLastOp! ctx' =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getNextBlock!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getNextBlock! ctx' =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =>]
theorem BlockPtr.getPrevBlock!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getPrevBlock! ctx' =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =>]
theorem OperationPtr.get!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.get! ctx' = operation.get! ctx := by
  grind

@[grind =>]
theorem OperationPtr.getNextOp!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getNextOp! ctx' =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[grind =>]
theorem OperationPtr.getPrevOp!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getPrevOp! ctx' =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[grind =>]
theorem OperationPtr.getParent!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getParent! ctx' =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[grind =>]
theorem OperationPtr.getAttributes!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getAttributes! ctx' =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getOpType!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getOpType! ctx' = operation.getOpType! ctx := by
  grind

@[grind =>]
theorem OperationPtr.getProperties!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getProperties! ctx' opCode = operation.getProperties! ctx opCode := by
  grind

@[grind =>]
theorem OperationPtr.getNumResults!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getNumResults! ctx' = operation.getNumResults! ctx := by
  grind

@[grind =>]
theorem OpResultPtr.get!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opResult.get! ctx' = opResult.get! ctx := by
  grind [Operation.default_results_eq]

@[grind =>]
theorem OpResultPtr.getIndex!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =>]
theorem OpResultPtr.getType!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =>]
theorem OpResultPtr.getFirstUse!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[grind =>]
theorem OpResultPtr.getOwner!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[grind =>]
theorem OperationPtr.getNumOperands!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtr.get!_RegionPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opOperand.get! ctx' = opOperand.get! ctx := by
  grind [Operation.default_operands_eq]

@[simp, grind =>]
theorem OpOperandPtr.getNextUse!_RegionPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getBack!_RegionPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getOwner!_RegionPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem OpOperandPtr.getValue!_RegionPtr_allocEmpty  {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =>]
theorem OperationPtr.getOperands!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getOperands! ctx' = operation.getOperands! ctx := by
  grind

@[grind =>]
theorem OperationPtr.getNumSuccessors!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getNumSuccessors! ctx' = operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =>]
theorem BlockOperandPtr.get!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockOperand.get! ctx' = blockOperand.get! ctx := by
  grind [Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getNextUse!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getBack!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getOwner!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem BlockOperandPtr.getValue!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[grind =>]
theorem OperationPtr.getNumRegions!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getNumRegions! ctx' = operation.getNumRegions! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.getRegion!_RegionPtr_allocEmpty  {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getRegion! ctx' i = operation.getRegion! ctx i := by
  grind [Operation.default_regions_eq]

@[simp, grind =>]
theorem BlockOperandPtrPtr.get!_RegionPtr_allocEmpty {blockOperandPtr : BlockOperandPtrPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockOperandPtr.get! ctx' = blockOperandPtr.get! ctx := by
  grind

@[simp, grind =>]
theorem BlockPtr.getNumArguments!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.get!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockArg.get! ctx' = blockArg.get! ctx := by
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getType!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.getIndex!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp]
theorem BlockArgumentPtr.getLoc!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (_heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockArg.getLoc! ctx' =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =>]
theorem BlockArgumentPtr.getOwner!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =>]
theorem RegionPtr.get!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    region.get! ctx' = if region = rg' then Region.empty else region.get! ctx := by
  grind

@[simp, grind =>]
theorem RegionPtr.getParent!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    region.getParent! ctx' =
    if region = rg' then none else region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind [Region.empty]

@[simp, grind =>]
theorem RegionPtr.getFirstBlock!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    region.getFirstBlock! ctx' =
    if region = rg' then none else region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind [Region.empty]

@[simp, grind =>]
theorem RegionPtr.getLastBlock!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    region.getLastBlock! ctx' =
    if region = rg' then none else region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind [Region.empty]

@[simp, grind =>]
theorem ValuePtr.getFirstUse!_RegionPtr_allocEmpty {value : ValuePtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind

@[simp, grind =>]
theorem ValuePtr.getType!_RegionPtr_allocEmpty {value : ValuePtr}
    (_ : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    value.getType! ctx' = value.getType! ctx := by
  grind

@[simp, grind =>]
theorem OpOperandPtrPtr.get!_RegionPtr_allocEmpty {opOperandPtr : OpOperandPtrPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind

/- RegionPtr.dealloc -/

@[simp, grind =]
theorem BlockPtr.get!_RegionPtr_dealloc {block : BlockPtr} :
    block.get! (RegionPtr.dealloc region' ctx hregion') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_dealloc {block : BlockPtr} :
    block.getParent! (RegionPtr.dealloc region' ctx hregion') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_dealloc {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.dealloc region' ctx hregion') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_dealloc {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.dealloc region' ctx hregion') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_dealloc {block : BlockPtr} :
    block.getLastOp! (RegionPtr.dealloc region' ctx hregion') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_dealloc {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.dealloc region' ctx hregion') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_dealloc {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.dealloc region' ctx hregion') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem OperationPtr.get!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.get! (RegionPtr.dealloc region' ctx hregion') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.dealloc region' ctx hregion') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.dealloc region' ctx hregion') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getParent! (RegionPtr.dealloc region' ctx hregion') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.dealloc region' ctx hregion') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getOpType! (RegionPtr.dealloc region' ctx hregion') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getProperties! (RegionPtr.dealloc region' ctx hregion') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getNumResults! (RegionPtr.dealloc region' ctx hregion') =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_RegionPtr_dealloc {opResult : OpResultPtr} :
    opResult.get! (RegionPtr.dealloc region' ctx hregion') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_dealloc {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.dealloc region' ctx hregion') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_dealloc {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.dealloc region' ctx hregion') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_dealloc {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.dealloc region' ctx hregion') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_dealloc {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.dealloc region' ctx hregion') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.dealloc region' ctx hregion') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_RegionPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.get! (RegionPtr.dealloc region' ctx hregion') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.dealloc region' ctx hregion') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.dealloc region' ctx hregion') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.dealloc region' ctx hregion') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.dealloc region' ctx hregion') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getOperands! (RegionPtr.dealloc region' ctx hregion') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getNumSuccessors! (RegionPtr.dealloc region' ctx hregion') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_RegionPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.get! (RegionPtr.dealloc region' ctx hregion') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.dealloc region' ctx hregion') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.dealloc region' ctx hregion') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.dealloc region' ctx hregion') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.dealloc region' ctx hregion') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getNumRegions! (RegionPtr.dealloc region' ctx hregion') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_RegionPtr_dealloc {operation : OperationPtr} :
    operation.getRegion! (RegionPtr.dealloc region' ctx hregion') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_RegionPtr_dealloc {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (RegionPtr.dealloc region' ctx hregion') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_RegionPtr_dealloc {block : BlockPtr} :
    block.getNumArguments! (RegionPtr.dealloc region' ctx hregion') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_RegionPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.get! (RegionPtr.dealloc region' ctx hregion') =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getType! (RegionPtr.dealloc region' ctx hregion') =
    blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (RegionPtr.dealloc region' ctx hregion') =
    blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (RegionPtr.dealloc region' ctx hregion') =
    blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (RegionPtr.dealloc region' ctx hregion') =
    blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (RegionPtr.dealloc region' ctx hregion') =
    blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_RegionPtr_dealloc {region : RegionPtr} :
    region.InBounds (RegionPtr.dealloc region' ctx hregion') →
    region.get! (RegionPtr.dealloc region' ctx hregion') =
    region.get! ctx := by
  grind [RegionPtr.InBounds]

@[simp, grind =]
theorem RegionPtr.getParent!_RegionPtr_dealloc {region : RegionPtr} :
    region.InBounds (RegionPtr.dealloc region' ctx hregion') →
    region.getParent! (RegionPtr.dealloc region' ctx hregion') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_dealloc {region : RegionPtr} :
    region.InBounds (RegionPtr.dealloc region' ctx hregion') →
    region.getFirstBlock! (RegionPtr.dealloc region' ctx hregion') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_dealloc {region : RegionPtr} :
    region.InBounds (RegionPtr.dealloc region' ctx hregion') →
    region.getLastBlock! (RegionPtr.dealloc region' ctx hregion') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_RegionPtr_dealloc {value : ValuePtr} :
    value.getFirstUse! (RegionPtr.dealloc region' ctx hregion') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_RegionPtr_dealloc {value : ValuePtr} :
    value.getType! (RegionPtr.dealloc region' ctx hregion') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_RegionPtr_dealloc {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (RegionPtr.dealloc region' ctx hregion') =
    opOperandPtr.get! ctx := by
  grind

/- RegionPtr.setParent -/

@[simp, grind =]
theorem BlockPtr.get!_RegionPtr_setParent {block : BlockPtr} :
    block.get! (RegionPtr.setParent region' ctx newParent hregion') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_setParent {block : BlockPtr} :
    block.getParent! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_setParent {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_setParent {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_setParent {block : BlockPtr} :
    block.getLastOp! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_setParent {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_setParent {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem OperationPtr.get!_RegionPtr_setParent {operation : OperationPtr} :
    operation.get! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getParent! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getOpType! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getProperties! (RegionPtr.setParent region' ctx newParent hregion') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNumResults! (RegionPtr.setParent region' ctx hregion' newParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.get! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.setParent region' ctx hregion' newParent) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.get! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getOperands! (RegionPtr.setParent region' ctx hregion' newParent) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNumSuccessors! (RegionPtr.setParent region' ctx hregion' newParent) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNumRegions! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getRegion! (RegionPtr.setParent region' ctx newParent hregion') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_RegionPtr_setParent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_RegionPtr_setParent {block : BlockPtr} :
    block.getNumArguments! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_RegionPtr_setParent {arg : BlockArgumentPtr} :
    arg.get! (RegionPtr.setParent region' ctx newParent hregion') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_setParent {arg : BlockArgumentPtr} :
    arg.getType! (RegionPtr.setParent region' ctx newParent hregion') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_setParent {arg : BlockArgumentPtr} :
    arg.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_setParent {arg : BlockArgumentPtr} :
    arg.getIndex! (RegionPtr.setParent region' ctx newParent hregion') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_setParent {arg : BlockArgumentPtr} :
    arg.getLoc! (RegionPtr.setParent region' ctx newParent hregion') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_setParent {arg : BlockArgumentPtr} :
    arg.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[grind =]
theorem RegionPtr.get!_RegionPtr_setParent {region : RegionPtr} :
    region.get! (RegionPtr.setParent region' ctx newParent hregion') =
    if region' = region then
      { region.get! ctx with parent := newParent }
    else
      region.get! ctx := by
  grind

@[grind =]
theorem RegionPtr.getParent!_RegionPtr_setParent {region : RegionPtr} :
    region.getParent! (RegionPtr.setParent region' ctx newParent hregion') =
    if region' = region then newParent else region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_setParent {region : RegionPtr} :
    region.getFirstBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_setParent {region : RegionPtr} :
    region.getLastBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_RegionPtr_setParent {value : ValuePtr} :
    value.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_RegionPtr_setParent {value : ValuePtr} :
    value.getType! (RegionPtr.setParent region' ctx newParent hregion') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_RegionPtr_setParent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (RegionPtr.setParent region' ctx hregion' newParent) =
    opOperandPtr.get! ctx := by
  grind

/- RegionPtr.setFirstBlock -/

@[simp, grind =]
theorem BlockPtr.get!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getParent! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getLastOp! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem OperationPtr.get!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getParent! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getOpType! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getProperties! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNumResults! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getOperands! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNumSuccessors! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNumRegions! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getRegion! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_RegionPtr_setFirstBlock {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getNumArguments! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_RegionPtr_setFirstBlock {arg : BlockArgumentPtr} :
    arg.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_setFirstBlock {arg : BlockArgumentPtr} :
    arg.getType! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_setFirstBlock {arg : BlockArgumentPtr} :
    arg.getFirstUse! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_setFirstBlock {arg : BlockArgumentPtr} :
    arg.getIndex! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_setFirstBlock {arg : BlockArgumentPtr} :
    arg.getLoc! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_setFirstBlock {arg : BlockArgumentPtr} :
    arg.getOwner! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[grind =]
theorem RegionPtr.get!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.get! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    if region' = region then
      { region.get! ctx with firstBlock := newFirstBlock }
    else
      region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.getParent! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.getFirstBlock! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    if region' = region then newFirstBlock else region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.getLastBlock! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_RegionPtr_setFirstBlock {value : ValuePtr} :
    value.getFirstUse! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_RegionPtr_setFirstBlock {value : ValuePtr} :
    value.getType! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_RegionPtr_setFirstBlock {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opOperandPtr.get! ctx := by
  grind


/- RegionPtr.setLastBlock -/

@[simp, grind =]
theorem BlockPtr.get!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getParent! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getLastOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem OperationPtr.get!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getParent! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getOpType! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getProperties! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNumResults! (RegionPtr.setLastBlock region' ctx hregion' newLastBlock) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.setLastBlock region' ctx hregion' newLastBlock) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getOperands! (RegionPtr.setLastBlock region' ctx hregion' newLastBlock) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNumSuccessors! (RegionPtr.setLastBlock region' ctx hregion' newLastBlock) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNumRegions! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getRegion! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_RegionPtr_setLastBlock {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getNumArguments! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_RegionPtr_setLastBlock {arg : BlockArgumentPtr} :
    arg.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_setLastBlock {arg : BlockArgumentPtr} :
    arg.getType! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_setLastBlock {arg : BlockArgumentPtr} :
    arg.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_setLastBlock {arg : BlockArgumentPtr} :
    arg.getIndex! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_setLastBlock {arg : BlockArgumentPtr} :
    arg.getLoc! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_setLastBlock {arg : BlockArgumentPtr} :
    arg.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[grind =]
theorem RegionPtr.get!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    if region' = region then
      { region.get! ctx with lastBlock := newLastBlock }
    else
      region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.getParent! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.getFirstBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.getLastBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    if region' = region then newLastBlock else region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_RegionPtr_setLastBlock {value : ValuePtr} :
    value.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_RegionPtr_setLastBlock {value : ValuePtr} :
    value.getType! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_RegionPtr_setLastBlock {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperandPtr.get! ctx := by
  grind

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
theorem BlockPtr.getParent!_ValuePtr_setType {block : BlockPtr} :
    block.getParent! (ValuePtr.setType value' ctx newType hvalue') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_ValuePtr_setType {block : BlockPtr} :
    block.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_ValuePtr_setType {block : BlockPtr} :
    block.getFirstOp! (ValuePtr.setType value' ctx newType hvalue') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_ValuePtr_setType {block : BlockPtr} :
    block.getLastOp! (ValuePtr.setType value' ctx newType hvalue') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_ValuePtr_setType {block : BlockPtr} :
    block.getNextBlock! (ValuePtr.setType value' ctx newType hvalue') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_ValuePtr_setType {block : BlockPtr} :
    block.getPrevBlock! (ValuePtr.setType value' ctx newType hvalue') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNextOp! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_ValuePtr_setType {operation : OperationPtr} :
    operation.getPrevOp! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_ValuePtr_setType {operation : OperationPtr} :
    operation.getParent! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_ValuePtr_setType {operation : OperationPtr} :
    operation.getAttributes! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_ValuePtr_setType {operation : OperationPtr} :
    operation.getOpType! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getIndex! (ValuePtr.setType value' ctx newType hvalue') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem OpResultPtr.getType!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getType! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = ValuePtr.opResult opResult then newType else opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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

@[grind =]
theorem BlockArgumentPtr.getType!_ValuePtr_setType {arg : BlockArgumentPtr} :
    arg.getType! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = ValuePtr.blockArgument arg then newType else arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_ValuePtr_setType {arg : BlockArgumentPtr} :
    arg.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_ValuePtr_setType {arg : BlockArgumentPtr} :
    arg.getIndex! (ValuePtr.setType value' ctx newType hvalue') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_ValuePtr_setType {arg : BlockArgumentPtr} :
    arg.getLoc! (ValuePtr.setType value' ctx newType hvalue') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_ValuePtr_setType {arg : BlockArgumentPtr} :
    arg.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_ValuePtr_setType {region : RegionPtr} :
    region.get! (ValuePtr.setType value' ctx newType hvalue') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_ValuePtr_setType {region : RegionPtr} :
    region.getParent! (ValuePtr.setType value' ctx newType hvalue') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_ValuePtr_setType {region : RegionPtr} :
    region.getFirstBlock! (ValuePtr.setType value' ctx newType hvalue') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_ValuePtr_setType {region : RegionPtr} :
    region.getLastBlock! (ValuePtr.setType value' ctx newType hvalue') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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
theorem BlockPtr.getParent!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getParent! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getOpType! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = ValuePtr.opResult opResult then newFirstUse else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_ValuePtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getType! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_ValuePtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = ValuePtr.blockArgument arg then newFirstUse else arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_ValuePtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getIndex! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_ValuePtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getLoc! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_ValuePtr_setFirstUse {arg : BlockArgumentPtr} :
    arg.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.get! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.getParent! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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


/- OpOperandPtrPtr.set -/

-- TODO: the match is elaborated in a strange way, with two arguments. Is it a Lean bug?
@[grind =]
theorem BlockPtr.get!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    match ptr' with
    | OpOperandPtrPtr.valueFirstUse (ValuePtr.blockArgument arg) =>
      if arg.block = block then
        { block.get! ctx with arguments :=
          (block.get! ctx).arguments.set! arg.index { arg.get! ctx with firstUse := newPtr } }
      else
        block.get! ctx
    | _ => block.get! ctx := by
  rcases ptr' with operand | ⟨result | arg⟩ <;> grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getParent! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getLastOp! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    match ptr' with
    | OpOperandPtrPtr.valueFirstUse (ValuePtr.opResult or) =>
      if or.op = operation then
        { operation.get! ctx with results :=
          (operation.get! ctx).results.set! or.index { or.get! ctx with firstUse := newPtr } }
      else
        operation.get! ctx
    | OpOperandPtrPtr.valueFirstUse (ValuePtr.blockArgument _) =>
      operation.get! ctx
    | OpOperandPtrPtr.operandNextUse operand =>
      if operand.op = operation then
        { operation.get! ctx with operands :=
          (operation.get! ctx).operands.set! operand.index { operand.get! ctx with nextUse := newPtr } }
      else
        operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getParent! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtrPtr.set value' ctx newPtr hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtrPtr.set value' ctx newPtr hvalue') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.operandNextUse opOperand then
      { opOperand.get! ctx with nextUse := newPtr }
    else
      opOperand.get! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.operandNextUse opOperand then newPtr else opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.valueFirstUse (ValuePtr.opResult opResult) then
      { opResult.get! ctx with firstUse := newPtr }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.valueFirstUse (ValuePtr.opResult opResult) then newPtr
    else opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getOperands! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumSuccessors! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumRegions! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getRegion! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtrPtr_set {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getNumArguments! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.valueFirstUse (ValuePtr.blockArgument arg) then
      { arg.get! ctx with firstUse := newPtr }
    else
      arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getType! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.valueFirstUse (ValuePtr.blockArgument arg) then newPtr else arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getIndex! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getLoc! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getOwner! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.getParent! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtrPtr_set {value : ValuePtr} :
    value.getFirstUse! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = OpOperandPtrPtr.valueFirstUse value then
      newPtr
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtrPtr_set {value : ValuePtr} :
    value.getType! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtrPtr_set {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if opOperandPtr = ptr' then
      newPtr
    else
      opOperandPtr.get! ctx := by
  grind

/- BlockOperandPtrPtr.set -/

-- TODO: the match is elaborated in a strange way, with two arguments. Is it a Lean bug?
@[grind =]
theorem BlockPtr.get!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    match ptr' with
    | BlockOperandPtrPtr.blockFirstUse block' =>
      if block = block' then
        { block.get! ctx with firstUse := newPtr }
      else
        block.get! ctx
    | _ => block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getParent! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    match ptr' with
    | BlockOperandPtrPtr.blockFirstUse block' =>
      if block = block' then newPtr else block.getFirstUse! ctx
    | _ => block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem BlockPtr.firstUse!_BlockOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr')).firstUse =
    if ptr' = BlockOperandPtrPtr.blockFirstUse block then
      newPtr
    else
      (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockOperandPtrPtr_set {block : BlockPtr} :
    (block.get! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[grind =]
theorem OperationPtr.get!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    match ptr' with
    | BlockOperandPtrPtr.blockOperandNextUse operand =>
      if operand.op = operation then
        { operation.get! ctx with blockOperands :=
          (operation.get! ctx).blockOperands.set! operand.index { operand.get! ctx with nextUse := newPtr } }
      else
        operation.get! ctx
    | _ =>
      operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtrPtr.set value' ctx newPtr hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtrPtr.set value' ctx newPtr hvalue') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getOperands! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getOperands! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = BlockOperandPtrPtr.blockOperandNextUse blockOperand then
      { blockOperand.get! ctx with nextUse := newPtr }
    else
      blockOperand.get! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = BlockOperandPtrPtr.blockOperandNextUse blockOperand then newPtr else blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumRegions! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getRegion! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') i =
    operation.getRegion! ctx i := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_BlockOperandPtrPtr_set {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if blockOperandPtr = ptr' then
      newPtr
    else
      blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getNumArguments! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getType! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtrPtr_set {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.getParent! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockOperandPtrPtr_set {value : ValuePtr} :
    value.getFirstUse! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockOperandPtrPtr_set {value : ValuePtr} :
    value.getType! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockOperandPtrPtr_set {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    opOperandPtr.get! ctx := by
  grind

/- OperationPtr.setNextOp -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setNextOp {block : BlockPtr} :
    block.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getParent! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
  grind

@[grind =]
theorem OperationPtr.get!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    if op' = operation then
      { operation.get! ctx with next := newNextOp }
    else
      operation.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    if op' = operation then newNextOp else operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_setNextOp {arg : BlockArgumentPtr} :
    arg.getType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setNextOp {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setNextOp {arg : BlockArgumentPtr} :
    arg.getIndex! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setNextOp {arg : BlockArgumentPtr} :
    arg.getLoc! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setNextOp {arg : BlockArgumentPtr} :
    arg.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setNextOp {region : RegionPtr} :
    region.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setNextOp {region : RegionPtr} :
    region.getParent! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setNextOp {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setNextOp {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getParent! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    if op' = operation then newPrevOp else operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_setPrevOp {arg : BlockArgumentPtr} :
    arg.getType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setPrevOp {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setPrevOp {arg : BlockArgumentPtr} :
    arg.getIndex! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setPrevOp {arg : BlockArgumentPtr} :
    arg.getLoc! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setPrevOp {arg : BlockArgumentPtr} :
    arg.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.getParent! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setParent {block : BlockPtr} :
    block.getParent! (OperationPtr.setParent op' ctx newParent hop') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setParent {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setParent {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setParent op' ctx newParent hop') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setParent {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setParent op' ctx newParent hop') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setParent {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setParent op' ctx newParent hop') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setParent {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setParent op' ctx newParent hop') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[grind =]
theorem OperationPtr.getParent!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setParent op' ctx newParent hop') =
    if op' = operation then newParent else operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_OperationPtr_setParent {arg : BlockArgumentPtr} :
    arg.getType! (OperationPtr.setParent op' ctx newParent hop') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setParent {arg : BlockArgumentPtr} :
    arg.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setParent {arg : BlockArgumentPtr} :
    arg.getIndex! (OperationPtr.setParent op' ctx newParent hop') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setParent {arg : BlockArgumentPtr} :
    arg.getLoc! (OperationPtr.setParent op' ctx newParent hop') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setParent {arg : BlockArgumentPtr} :
    arg.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_OperationPtr_setParent {region : RegionPtr} :
    region.get! (OperationPtr.setParent op' ctx newParent hop') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setParent {region : RegionPtr} :
    region.getParent! (OperationPtr.setParent op' ctx newParent hop') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setParent {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setParent op' ctx newParent hop') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setParent {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setParent op' ctx newParent hop') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- BlockOperandPtr.setNextUse -/

@[simp, grind =]
theorem BlockPtr.get!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setNextUse {operand : OpOperandPtr} :
    operand.getNextUse! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setNextUse {operand : OpOperandPtr} :
    operand.getBack! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setNextUse {operand : OpOperandPtr} :
    operand.getOwner! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setNextUse {operand : OpOperandPtr} :
    operand.getValue! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    if blockOperand = operand' then newNextUse else blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getType! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setNextUse {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.get! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    if blockOperand = operand' then newBack else blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getType! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setBack {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.get! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    if blockOperand = operand' then newOwner else blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getType! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setOwner {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.get! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getParent! ctx := by
  simp only [BlockPtr.getParent!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getFirstUse! ctx := by
  simp only [BlockPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getFirstOp! ctx := by
  simp only [BlockPtr.getFirstOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getLastOp! ctx := by
  simp only [BlockPtr.getLastOp!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getNextBlock! ctx := by
  simp only [BlockPtr.getNextBlock!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    block.getPrevBlock! ctx := by
  simp only [BlockPtr.getPrevBlock!_def]
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
theorem OperationPtr.getNextOp!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
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
theorem OperationPtr.getOpType!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getOpType! ctx := by
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
theorem OpResultPtr.getIndex!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
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
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
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
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    if blockOperand = operand' then newValue else blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
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
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getType! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getFirstUse! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getIndex! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getLoc! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setValue {arg : BlockArgumentPtr} :
    arg.getOwner! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    arg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.get! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
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

/- BlockPtr.setArguments -/

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_setArguments {block : BlockPtr} :
    (block.get! (BlockPtr.setArguments block' ctx newArguments hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_setArguments {block : BlockPtr} :
    (block.get! (BlockPtr.setArguments block' ctx newArguments hblock')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_setArguments {block : BlockPtr} :
    (block.get! (BlockPtr.setArguments block' ctx newArguments hblock')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_setArguments {block : BlockPtr} :
    (block.get! (BlockPtr.setArguments block' ctx newArguments hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_setArguments {block : BlockPtr} :
    (block.get! (BlockPtr.setArguments block' ctx newArguments hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_setArguments {block : BlockPtr} :
    (block.get! (BlockPtr.setArguments block' ctx newArguments hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setArguments block' ctx newArguments hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.setArguments operation' ctx hop' newOperands) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.setArguments block' ctx newOperands hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setArguments block' ctx newOperands hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setArguments block' ctx newOperands hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setArguments block' ctx newOperands hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setArguments block' ctx newOperands hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_setArguments {operation : OperationPtr} {hop} :
    operation.getNumRegions! (BlockPtr.setArguments op ctx newOperands hop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_setArguments {operation : OperationPtr} {hop} :
    operation.getRegion! (BlockPtr.setArguments op ctx newOperands hop) i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_setArguments {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_setArguments {block : BlockPtr} :
    block.getNumArguments! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if block = block' then
      newArguments.size
    else
      block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then
      newArguments[blockArg.index]!
    else
      blockArg.get! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then newArguments[blockArg.index]!.type else blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then newArguments[blockArg.index]!.firstUse else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then newArguments[blockArg.index]!.index else blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then newArguments[blockArg.index]!.loc else blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then newArguments[blockArg.index]!.owner else blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setArguments {region : RegionPtr} :
    region.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setArguments {region : RegionPtr} :
    region.getParent! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setArguments {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setArguments {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_setArguments {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    match value with
    | .blockArgument arg =>
      if arg.block = block' then
        newArguments[arg.index]!.firstUse
      else
        value.getFirstUse! ctx
    | .opResult _ =>
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_BlockPtr_setArguments {value : ValuePtr} :
    value.getType! (BlockPtr.setArguments block' ctx newArguments hblock') =
    match value with
    | .blockArgument arg =>
      if arg.block = block' then
        newArguments[arg.index]!.type
      else
        value.getType! ctx
    | .opResult _ =>
      value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_setArguments {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    match opOperandPtr with
    | .valueFirstUse (.blockArgument arg) =>
      if arg.block = block' then
        newArguments[arg.index]!.firstUse
      else
        opOperandPtr.get! ctx
    | _ =>
      opOperandPtr.get! ctx := by
  grind

/- OperationPtr.pushOperand -/

@[simp, grind =]
theorem BlockPtr.firstUse!_BlockPtr_pushArgument {block : BlockPtr} :
    (block.get! (BlockPtr.pushArgument block' ctx newArgument hblock')).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_BlockPtr_pushArgument {block : BlockPtr} :
    (block.get! (BlockPtr.pushArgument block' ctx newArgument hblock')).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_BlockPtr_pushArgument {block : BlockPtr} :
    (block.get! (BlockPtr.pushArgument block' ctx newArgument hblock')).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_BlockPtr_pushArgument {block : BlockPtr} :
    (block.get! (BlockPtr.pushArgument block' ctx newArgument hblock')).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_BlockPtr_pushArgument {block : BlockPtr} :
    (block.get! (BlockPtr.pushArgument block' ctx newArgument hblock')).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_BlockPtr_pushArgument {block : BlockPtr} :
    (block.get! (BlockPtr.pushArgument block' ctx newArgument hblock')).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getNextOp! ctx := by
  simp only [OperationPtr.getNextOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getPrevOp! ctx := by
  simp only [OperationPtr.getPrevOp!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getParent! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getParent! ctx := by
  simp only [OperationPtr.getParent!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getAttributes! ctx := by
  simp only [OperationPtr.getAttributes!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getOpType! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.pushArgument block' ctx newArgument hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNumResults! (BlockPtr.pushArgument operation' ctx hop' newOperands) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getType! ctx := by
  simp only [OpResultPtr.getType!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getFirstUse! ctx := by
  simp only [OpResultPtr.getFirstUse!_def]
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getOwner! ctx := by
  simp only [OpResultPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.pushArgument block' ctx newOperands hblock') =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.get! (BlockPtr.pushArgument block' ctx newOperand hblock') =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.pushArgument block' ctx newOperand hblock') =
    opOperand.getNextUse! ctx := by
  simp only [OpOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.pushArgument block' ctx newOperand hblock') =
    opOperand.getBack! ctx := by
  simp only [OpOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.pushArgument block' ctx newOperand hblock') =
    opOperand.getOwner! ctx := by
  simp only [OpOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.pushArgument block' ctx newOperand hblock') =
    opOperand.getValue! ctx := by
  simp only [OpOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getOperands! (BlockPtr.pushArgument block' ctx newOperands hblock') =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNumSuccessors! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getNextUse! ctx := by
  simp only [BlockOperandPtr.getNextUse!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getBack! ctx := by
  simp only [BlockOperandPtr.getBack!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getOwner! ctx := by
  simp only [BlockOperandPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getValue! ctx := by
  simp only [BlockOperandPtr.getValue!_def]
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNumRegions! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getRegion! (BlockPtr.pushArgument block' ctx newArgument hblock') i =
    operation.getRegion! ctx i := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockPtr_pushArgument {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperandPtr.get! ctx := by
  grind

@[grind =]
theorem BlockPtr.getNumArguments!_BlockPtr_pushArgument {block : BlockPtr} {hop} :
    block.getNumArguments! (BlockPtr.pushArgument op ctx newOperand hop) =
    if block = op then
      block.getNumArguments! ctx + 1
    else
      block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument! ctx then
      newArgument
    else
      blockArg.get! ctx := by
  grind [BlockPtr.getArgument]

@[grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument! ctx then newArgument.type else blockArg.getType! ctx := by
  simp only [BlockArgumentPtr.getType!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument! ctx then newArgument.firstUse else blockArg.getFirstUse! ctx := by
  simp only [BlockArgumentPtr.getFirstUse!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument! ctx then newArgument.index else blockArg.getIndex! ctx := by
  simp only [BlockArgumentPtr.getIndex!_def]
  grind

@[grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument! ctx then newArgument.loc else blockArg.getLoc! ctx := by
  simp only [BlockArgumentPtr.getLoc!_def] <;> grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument! ctx then newArgument.owner else blockArg.getOwner! ctx := by
  simp only [BlockArgumentPtr.getOwner!_def]
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_pushArgument {region : RegionPtr} :
    region.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_pushArgument {region : RegionPtr} :
    region.getParent! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.getParent! ctx := by
  simp only [RegionPtr.getParent!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_pushArgument {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.getFirstBlock! ctx := by
  simp only [RegionPtr.getFirstBlock!_def]
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_pushArgument {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.getLastBlock! ctx := by
  simp only [RegionPtr.getLastBlock!_def]
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_pushArgument {value : ValuePtr} :
    value.getFirstUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if value = .blockArgument { block := block', index := block'.getNumArguments! ctx} then
      newArgument.firstUse
    else
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_BlockPtr_pushArgument {value : ValuePtr} :
    value.getType! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if value = .blockArgument { block := block', index := block'.getNumArguments! ctx} then
      newArgument.type
    else
      value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_BlockPtr_pushArgument {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if opOperandPtr = .valueFirstUse (.blockArgument { block := block', index := block'.getNumArguments! ctx}) then
      newArgument.firstUse
    else
      opOperandPtr.get! ctx := by
  grind
