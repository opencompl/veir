module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

/- OperationPtr.setOperands -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setOperands {block : BlockPtr} :
    block.get! (OperationPtr.setOperands operation' ctx hop' newOperands) =
    block.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_setOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setOperands operation' ctx newOperands hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_setOperands {region : RegionPtr} :
    region.get! (OperationPtr.setOperands operation' ctx newOperands hop') =
    region.get! ctx := by
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

@[grind =]
theorem OperationPtr.get!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    if operation = operation' then
      { operation.get! ctx with operands := (operation.get! ctx).operands.push newOperand }
    else
      operation.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_pushOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushOperand operation' ctx newOperand hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_pushOperand {region : RegionPtr} :
    region.get! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    region.get! ctx := by
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

@[grind =]
theorem OperationPtr.get!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    if operation = operation' then
      {operation.get! ctx with blockOperands := newOperands}
    else
      operation.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    (operation.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.get! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    region.get! ctx := by
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

@[grind =]
theorem OperationPtr.get!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if operation = operation' then
      {operation.get! ctx with blockOperands := (operation.get! ctx).blockOperands.push newOperand}
    else
      operation.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    region.get! ctx := by
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
    if blockArg.block = block' then
      if blockArg.index = (block'.getNumArguments! ctx) then
        newArgument
      else
        blockArg.get! ctx
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_pushArgument {region : RegionPtr} :
    region.get! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.get! ctx := by
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
