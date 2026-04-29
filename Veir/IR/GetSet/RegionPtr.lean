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
theorem BlockPtr.get!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    block.get! ctx' = block.get! ctx := by
  grind

@[grind =>]
theorem OperationPtr.get!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.get! ctx' = operation.get! ctx := by
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
theorem RegionPtr.get!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    region.get! ctx' = if region = rg' then Region.empty else region.get! ctx := by
  grind

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

/- RegionPtr.setParent -/

@[simp, grind =]
theorem BlockPtr.get!_RegionPtr_setParent {block : BlockPtr} :
    block.get! (RegionPtr.setParent region' ctx newParent hregion') =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_RegionPtr_setParent {operation : OperationPtr} :
    operation.get! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.get! ctx := by
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

@[grind =]
theorem RegionPtr.get!_RegionPtr_setParent {region : RegionPtr} :
    region.get! (RegionPtr.setParent region' ctx newParent hregion') =
    if region' = region then
      { region.get! ctx with parent := newParent }
    else
      region.get! ctx := by
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
theorem OperationPtr.get!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.get! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.get! ctx := by
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

@[grind =]
theorem RegionPtr.get!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.get! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    if region' = region then
      { region.get! ctx with firstBlock := newFirstBlock }
    else
      region.get! ctx := by
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
theorem OperationPtr.get!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.get! ctx := by
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

@[grind =]
theorem RegionPtr.get!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.get! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    if region' = region then
      { region.get! ctx with lastBlock := newLastBlock }
    else
      region.get! ctx := by
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

