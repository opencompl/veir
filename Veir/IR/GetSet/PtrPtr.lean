module

public import Veir.IR.Basic
import all Veir.IR.Basic
import Veir.IR.GetSet.ValuePtr

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx': IRContext OpInfo}

public section

setup_grind_with_get_set_definitions

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

