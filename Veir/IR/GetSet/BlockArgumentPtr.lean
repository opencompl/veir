module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

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

