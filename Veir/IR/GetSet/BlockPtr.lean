module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

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

