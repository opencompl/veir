module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

public section

setup_grind_with_get_set_definitions

/-
 - The getters we consider are:
 - * BlockPtr.get! with optionally special cases for:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! with optionally special cases for:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * Operation.opType
 -   * Operation.attrs
 - * Operation.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get!
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get! with optionally special cases for:
 -   * firstBlock
 -   * lastBlock
 -   * parent
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/

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
    (h : OperationPtr.allocEmpty ctx ty = some (ctx', op')) :
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

/- OperationPtr.setProperties -/

@[simp, grind =]
<<<<<<< HEAD
=======
theorem IRContext.topLevelOp_OperationPtr_setProperties :
    (OperationPtr.setProperties operation' ctx newProperties inBounds hprop).topLevelOp =
    ctx.topLevelOp := by
  grind

@[simp, grind =]
>>>>>>> e86c4fb (GetSet and InBounds)
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

/- OperationPtr.setRegions -/

@[simp, grind =]
theorem BlockPtr.get!_OperationPtr_setRegions {block : BlockPtr} :
    block.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    block.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_setRegions {operation : OperationPtr} :
    (operation.get! (OperationPtr.setRegions operation' ctx newRegions hop')).opType =
    (operation.get! ctx).opType := by
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
theorem OperationPtr.getNumSuccessors!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumSuccessors! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    blockOperand.get! ctx := by
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
theorem RegionPtr.get!_OperationPtr_setRegions {region : RegionPtr} :
    region.get! (OperationPtr.setRegions operation' ctx newRegions hop') =
    region.get! ctx := by
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

@[simp, grind =]
theorem RegionPtr.get!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.get! (BlockArgumentPtr.setType arg' ctx newType harg') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.get! (BlockArgumentPtr.setFirstUse arg' ctx newFirstUse harg') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.get! (BlockArgumentPtr.setLoc arg' ctx newLoc harg') =
    region.get! ctx := by
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

@[simp, grind =>]
theorem OperationPtr.get!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.get! ctx' = operation.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    region.get! ctx' = region.get! ctx := by
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

/- BlockPtr.setParent -/

@[grind =]
theorem BlockPtr.get!_BlockPtr_setParent {block : BlockPtr} :
    block.get! (BlockPtr.setParent block' ctx newParent hblock') =
    if block' = block then
      { block.get! ctx with parent := newParent }
    else
      block.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_setParent {region : RegionPtr} :
    region.get! (BlockPtr.setParent block' ctx newParent hblock') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.get! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.get! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_setLastOp {region : RegionPtr} :
    region.get! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.get! (BlockPtr.setNextBlock block' ctx newNextBlock hblock') =
    region.get! ctx := by
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
theorem RegionPtr.get!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.get! (BlockPtr.setPrevBlock block' ctx newPrevBlock hblock') =
    region.get! ctx := by
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
  cases ptr'
  · grind
  · split
    · grind
    · simp only [OpOperandPtrPtr.set_valueFirstUse, get!_ValuePtr_setFirstUse,
      Array.set!_eq_setIfInBounds]
      split <;> grind

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
theorem OperationPtr.opType!_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).opType =
    (operation.get! ctx).opType := by
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
theorem OperationPtr.getNumOperands!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    blockOperand.get! ctx := by
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
theorem RegionPtr.get!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.get! (OpOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.get! ctx := by
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
theorem OperationPtr.opType!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).opType =
    (operation.get! ctx).opType := by
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
theorem OperationPtr.getNumOperands!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    if ptr' = BlockOperandPtrPtr.blockOperandNextUse blockOperand then
      { blockOperand.get! ctx with nextUse := newPtr }
    else
      blockOperand.get! ctx := by
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
theorem RegionPtr.get!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.get! (BlockOperandPtrPtr.set ptr' ctx newPtr hptr') =
    region.get! ctx := by
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

@[grind =]
theorem OperationPtr.get!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    if op' = operation then
      { operation.get! ctx with next := newNextOp }
    else
      operation.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_setNextOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setNextOp op' ctx newNextOp hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_setNextOp {region : RegionPtr} :
    region.get! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.get! ctx := by
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

@[grind =]
theorem OperationPtr.get!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    if op' = operation then
      { operation.get! ctx with prev := newPrevOp }
    else
      operation.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_setPrevOp {operation : OperationPtr} :
    (operation.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.get! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.get! ctx := by
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

@[grind =]
theorem OperationPtr.get!_OperationPtr_setParent {operation : OperationPtr} :
    operation.get! (OperationPtr.setParent op' ctx newParent hop') =
    if op' = operation then
      { operation.get! ctx with parent := newParent }
    else
      operation.get! ctx := by
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
theorem OperationPtr.opType!_OperationPtr_setParent {operation : OperationPtr} :
    (operation.get! (OperationPtr.setParent op' ctx newParent hop')).opType =
    (operation.get! ctx).opType := by
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
theorem RegionPtr.get!_OperationPtr_setParent {region : RegionPtr} :
    region.get! (OperationPtr.setParent op' ctx newParent hop') =
    region.get! ctx := by
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
theorem OperationPtr.getProperties!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getProperties! (BlockPtr.setArguments block' ctx newArguments hblock') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.get! ctx := by
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

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_setArguments {region : RegionPtr} :
    region.get! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.get! ctx := by
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
