module

public import Veir.IR.Basic
import all Veir.IR.Basic

namespace Veir

variable {OpInfo : Type} [IsOpCode OpInfo]
variable {ctx ctx': IRContext OpInfo}
variable {Dialect : Type} [IsOpCode Dialect] [HasDialect OpInfo Dialect]
variable {opCode opCode' : Dialect}

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
 -   * Operation.attrs
 - * OperationPtr.getOpType!
 - * OperationPtr.getProperties!
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get!
 - * OperationPtr.getOperands!
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

variable {CreateDialect : Type} [IsOpCode CreateDialect]
  [HasDialect OpInfo CreateDialect]
variable {ty : CreateDialect} {properties : propertiesOf ty}

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
theorem OperationPtr.getNumOperands!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNumOperands! ctx' =
    if operation = op' then 0 else operation.getNumOperands! ctx := by
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
theorem BlockPtr.getNumArguments!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getNumArguments! ctx' = block.getNumArguments! ctx := by
  grind

/- OperationPtr.dealloc -/

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
theorem BlockPtr.getNumArguments!_OperationPtr_dealloc {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.dealloc operation' ctx hop') =
    block.getNumArguments! ctx := by
  grind

/- OperationPtr.setOperands -/

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setOperands operation' ctx newOperands hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setOperands operation' ctx newOperands hop') =
    operation.getNumResults! ctx := by
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
        opOperand.getNextUse! ctx := by
  grind

/- OperationPtr.pushOperand -/

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushOperand operation' ctx newOperand hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.pushOperand operation' ctx hop' newOperands) =
    operation.getNumResults! ctx := by
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
theorem ValuePtr.getFirstUse!_OperationPtr_pushOperand {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_pushOperand {value : ValuePtr} :
    value.getType! (OperationPtr.pushOperand operation' ctx newOperand hop') =
    value.getType! ctx := by
  grind

/- OperationPtr.setBlockOperands -/

@[simp, grind =]
theorem OperationPtr.getProperties!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setBlockOperands operation' ctx newOperands hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setBlockOperands operation' ctx newOperands hop') =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.pushBlockOperand operation' ctx hop' newOperands) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushBlockOperand operation' ctx hop' newOperands) =
    operation.getNumOperands! ctx := by
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

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getNumArguments! (OperationPtr.pushBlockOperand op ctx newOperand hop) =
    block.getNumArguments! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setResults operation' ctx newResults hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getOpType! ctx := by
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
theorem OperationPtr.getNumOperands!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setResults operation' ctx newResults hop') =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.pushResult operation' ctx newResult hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getOpType! ctx := by
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
theorem OperationPtr.getNumOperands!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushResult operation' ctx newResult hop') =
    operation.getNumOperands! ctx := by
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

@[grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_pushResult {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OperationPtr.pushResult op ctx newResult hop) =
    if opOperandPtr = .valueFirstUse (ValuePtr.opResult (op.nextResult ctx)) then
      newResult.firstUse
    else
      opOperandPtr.get! ctx := by
  grind [OperationPtr.getResult]

/- OperationPtr.setProperties -/

section OperationPtr.setProperties

variable {operation' : OperationPtr}
variable {newProperties : propertiesOf opCode}
variable {inBounds : operation'.InBounds ctx}
variable {hprop : operation'.getOpType! ctx = opCode}

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
theorem OperationPtr.getOpType!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setProperties operation' ctx opCode newProperties inBounds hprop) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getOpType!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getOpType! ctx := by
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
theorem OperationPtr.getNumOperands!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setAttributes operation' ctx newAttrs opIn) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setRegions operation' ctx newRegions hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setRegions operation' ctx newRegions hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setRegions operation' ctx hop' newRegions) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setRegions operation' ctx hop' newRegions) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getOpType!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.pushRegion operation' ctx newRegion hop') =
    operation.getOpType! ctx := by
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
theorem OperationPtr.getNumOperands!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.pushRegion operation' ctx hop' newRegion) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNumOperands! (BlockArgumentPtr.setType arg' ctx harg' newType) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (BlockArgumentPtr.setFirstUse arg' ctx harg' newFirstUse) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNumOperands! (BlockArgumentPtr.setLoc arg' ctx harg' newLoc) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl)) :
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
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
theorem OpOperandPtrPtr.get!_BlockPtr_allocEmpty {opOperandPtr : OpOperandPtrPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind [Block.default_arguments_eq]

/- BlockPtr.setParent -/

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
theorem OperationPtr.getNumOperands!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setParent block' ctx hblock' newParent) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setFirstUse block' ctx hblock' newFirstUse) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setFirstOp block' ctx hblock' newFirstOp) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setLastOp block' ctx hblock' newLastOp) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setNextBlock block' ctx hblock' newNextBlock) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setPrevBlock block' ctx hblock' newPrevBlock) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setBack operand' ctx newBack hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtr.setValue operand' ctx newValue hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumOperands! (OpOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getProperties! (OpResultPtr.setType result' ctx newType hresult') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getOpType! (OpResultPtr.setType result' ctx newType hresult') =
    operation.getOpType! ctx := by
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

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNumOperands! (OpResultPtr.setType result' ctx hresult' newType) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getProperties! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getOpType! (OpResultPtr.setFirstUse result' ctx newFirstUse hresult') =
    operation.getOpType! ctx := by
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

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (OpResultPtr.setFirstUse result' ctx hresult' newFirstUse) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', rg')) :
    operation.getNumOperands! ctx' = operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.setParent region' ctx hregion' newParent) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.setFirstBlock region' ctx hregion' newFirstBlock) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNumOperands! (RegionPtr.setLastBlock region' ctx hregion' newLastBlock) =
    operation.getNumOperands! ctx := by
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

@[simp, grind =]
theorem OperationPtr.getProperties!_ValuePtr_setType {operation : OperationPtr} :
    operation.getProperties! (ValuePtr.setType value' ctx newType hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_ValuePtr_setType {operation : OperationPtr} :
    operation.getOpType! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getOpType! ctx := by
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

@[simp, grind =]
theorem OperationPtr.getNumOperands!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNumOperands! (ValuePtr.setType value' ctx hvalue' newType) =
    operation.getNumOperands! ctx := by
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

@[simp, grind =]
theorem OperationPtr.getProperties!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getProperties! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getOpType! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getOpType! ctx := by
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

@[simp, grind =]
theorem OperationPtr.getNumOperands!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNumOperands! (ValuePtr.setFirstUse value' ctx hvalue' newFirstUse) =
    operation.getNumOperands! ctx := by
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
@[simp, grind =]
theorem OperationPtr.getProperties!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getProperties! (OpOperandPtrPtr.set value' ctx newPtr hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getOpType! (OpOperandPtrPtr.set value' ctx newPtr hvalue') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_OpOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (OpOperandPtrPtr.set value' ctx newPtr hvalue')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumResults! (OpOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumResults! ctx := by
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
@[simp, grind =]
theorem OperationPtr.getProperties!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtrPtr.set value' ctx newPtr hvalue') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtrPtr.set value' ctx newPtr hvalue') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.results!.size_BlockOperandPtrPtr_set {operation : OperationPtr} :
    (operation.get! (BlockOperandPtrPtr.set value' ctx newPtr hvalue')).results.size =
    (operation.get! ctx).results.size := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtrPtr.set ptr' ctx hptr' newPtr) =
    operation.getNumResults! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setNextOp op' ctx newNextOp hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setNextOp op' ctx hop' newNextOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setNextOp op' ctx hop' newNextOp) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setPrevOp op' ctx newPrevOp hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setPrevOp op' ctx hop' newPrevOp) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setPrevOp op' ctx hop' newPrevOp) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getProperties! (OperationPtr.setParent op' ctx newParent hop') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getOpType! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNumResults! (OperationPtr.setParent op' ctx hop' newParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNumOperands! (OperationPtr.setParent op' ctx hop' newParent) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setNextUse operand' ctx newNextUse hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setNextUse operand' ctx hoperand' newNextUse) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setBack operand' ctx newBack hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setBack operand' ctx newBack hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setBack operand' ctx hoperand' newBack) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setOwner operand' ctx newOwner hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setOwner operand' ctx hoperand' newOwner) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getProperties!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getProperties! (BlockOperandPtr.setValue operand' ctx newValue hoperand') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getOpType! (BlockOperandPtr.setValue operand' ctx newValue hoperand') =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumResults! (BlockOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNumOperands! (BlockOperandPtr.setValue operand' ctx hoperand' newValue) =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getNumOperands! ctx := by
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
theorem OperationPtr.getNumOperands!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNumOperands! (BlockPtr.pushArgument block' ctx newOperands hblock') =
    operation.getNumOperands! ctx := by
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

/-
 - Lemmas relating the field getters with the operations that modify the IR context.
 - Lemmas already stated above (same name) are not repeated.
 - The field getters we consider are:
 - * OperationPtr.getNextOp!
 - * OperationPtr.getPrevOp!
 - * OperationPtr.getParent!
 - * OperationPtr.getRegions!
 - * OperationPtr.getAttributes!
 - * OperationPtr.getProperties!
 - * OpOperandPtr.getNextUse!
 - * OpOperandPtr.getBack!
 - * OpOperandPtr.getOwner!
 - * OpOperandPtr.getValue!
 - * BlockOperandPtr.getNextUse!
 - * BlockOperandPtr.getBack!
 - * BlockOperandPtr.getOwner!
 - * BlockOperandPtr.getValue!
 - * OpResultPtr.getType!
 - * OpResultPtr.getFirstUse!
 - * OpResultPtr.getOwner!
 - * BlockPtr.getParent!
 - * BlockPtr.getFirstUse!
 - * BlockPtr.getFirstOp!
 - * BlockPtr.getLastOp!
 - * BlockPtr.getNextBlock!
 - * BlockPtr.getPrevBlock!
 - * BlockArgumentPtr.getType!
 - * BlockArgumentPtr.getFirstUse!
 - * BlockArgumentPtr.getIndex!
 - * BlockArgumentPtr.getLoc!
 - * BlockArgumentPtr.getOwner!
 - * ValuePtr.getType!
 - * ValuePtr.getFirstUse!
 - * OpOperandPtrPtr.get!
 - * BlockOperandPtrPtr.get!
 - * RegionPtr.getParent!
 - * RegionPtr.getFirstBlock!
 - * RegionPtr.getLastBlock!
 -/

/- OperationPtr.setNextOp -/

@[grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    if operation = op' then
      newNextOp
    else
      operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setNextOp {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setNextOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setNextOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setNextOp {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getParent! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setNextOp {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setNextOp {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setNextOp {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setNextOp {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setNextOp {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setNextOp {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setNextOp {region : RegionPtr} :
    region.getParent! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setNextOp {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setNextOp {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setNextOp op' ctx newNextOp hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setPrevOp -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getNextOp! ctx := by
  grind

@[grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    if operation = op' then
      newPrevOp
    else
      operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setPrevOp {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setPrevOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setPrevOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setPrevOp {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getParent! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setPrevOp {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setPrevOp {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setPrevOp {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setPrevOp {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setPrevOp {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setPrevOp {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.getParent! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setPrevOp {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setPrevOp op' ctx newPrevOp hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setParent -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getPrevOp! ctx := by
  grind

@[grind =]
theorem OperationPtr.getParent!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setParent op' ctx newParent hop') =
    if operation = op' then
      newParent
    else
      operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setParent {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setParent op' ctx newParent hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setParent op' ctx newParent hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setParent op' ctx newParent hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setParent {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setParent op' ctx newParent hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setParent {block : BlockPtr} :
    block.getParent! (OperationPtr.setParent op' ctx newParent hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setParent {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setParent {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setParent op' ctx newParent hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setParent {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setParent op' ctx newParent hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setParent {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setParent op' ctx newParent hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setParent {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setParent op' ctx newParent hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setParent op' ctx newParent hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setParent op' ctx newParent hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setParent op' ctx newParent hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setParent op' ctx newParent hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setParent op' ctx newParent hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setParent {region : RegionPtr} :
    region.getParent! (OperationPtr.setParent op' ctx newParent hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setParent {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setParent op' ctx newParent hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setParent {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setParent op' ctx newParent hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setRegions -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setRegions op' ctx newRegions hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setRegions op' ctx newRegions hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setRegions op' ctx newRegions hop') =
    operation.getParent! ctx := by
  grind

@[grind =]
theorem OperationPtr.getRegions!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setRegions op' ctx newRegions hop') =
    if operation = op' then
      newRegions
    else
      operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setRegions {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setRegions op' ctx newRegions hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setRegions op' ctx newRegions hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setRegions op' ctx newRegions hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setRegions op' ctx newRegions hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setRegions {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setRegions op' ctx newRegions hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setRegions {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setRegions op' ctx newRegions hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setRegions op' ctx newRegions hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setRegions op' ctx newRegions hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setRegions {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setRegions op' ctx newRegions hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setRegions {block : BlockPtr} :
    block.getParent! (OperationPtr.setRegions op' ctx newRegions hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setRegions {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setRegions op' ctx newRegions hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setRegions {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setRegions op' ctx newRegions hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setRegions {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setRegions op' ctx newRegions hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setRegions {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setRegions op' ctx newRegions hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setRegions {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setRegions op' ctx newRegions hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setRegions {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setRegions op' ctx newRegions hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setRegions {region : RegionPtr} :
    region.getParent! (OperationPtr.setRegions op' ctx newRegions hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setRegions {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setRegions op' ctx newRegions hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setRegions {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setRegions op' ctx newRegions hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setAttributes -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    operation.getRegions! ctx := by
  grind

@[grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setAttributes {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    if operation = op' then
      newAttrs
    else
      operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setAttributes {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setAttributes {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setAttributes {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getParent! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setAttributes {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setAttributes {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setAttributes {region : RegionPtr} :
    region.getParent! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setAttributes {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setAttributes {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setAttributes op' ctx newAttrs hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setProperties -/

section OperationPtr.setProperties

variable {op' : OperationPtr}
variable {newProperties : propertiesOf opCode}
variable {hop' : op'.InBounds ctx}
variable {hprop : op'.getOpType! ctx = opCode}

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setProperties {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setProperties {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setProperties {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setProperties {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setProperties {block : BlockPtr} :
    block.getParent! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setProperties {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setProperties {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setProperties {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setProperties {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setProperties {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setProperties {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setProperties {region : RegionPtr} :
    region.getParent! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setProperties {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setProperties {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setProperties op' ctx opCode newProperties hop' hprop) =
    region.getLastBlock! ctx := by
  grind

end OperationPtr.setProperties

/- OperationPtr.setResults -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setResults op' ctx newResults hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setResults op' ctx newResults hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setResults op' ctx newResults hop') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setResults op' ctx newResults hop') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setResults {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setResults op' ctx newResults hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setResults {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setResults op' ctx newResults hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setResults {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setResults op' ctx newResults hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setResults {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setResults op' ctx newResults hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setResults {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setResults op' ctx newResults hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setResults op' ctx newResults hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setResults op' ctx newResults hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setResults op' ctx newResults hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setResults {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setResults op' ctx newResults hop') =
    blockOperand.getValue! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getType!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setResults op' ctx newResults hop') =
    if opResult.op = op' then
      newResults[opResult.index]!.type
    else
      opResult.getType! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setResults op' ctx newResults hop') =
    if opResult.op = op' then
      newResults[opResult.index]!.firstUse
    else
      opResult.getFirstUse! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setResults op' ctx newResults hop') =
    if opResult.op = op' then
      newResults[opResult.index]!.owner
    else
      opResult.getOwner! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setResults {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setResults op' ctx newResults hop') =
    if opResult.op = op' then
      newResults[opResult.index]!.index
    else
      opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setResults {block : BlockPtr} :
    block.getParent! (OperationPtr.setResults op' ctx newResults hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setResults {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setResults op' ctx newResults hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setResults {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setResults op' ctx newResults hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setResults {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setResults op' ctx newResults hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setResults {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setResults op' ctx newResults hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setResults {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setResults op' ctx newResults hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setResults op' ctx newResults hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setResults op' ctx newResults hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setResults op' ctx newResults hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setResults op' ctx newResults hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setResults {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setResults op' ctx newResults hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setResults {region : RegionPtr} :
    region.getParent! (OperationPtr.setResults op' ctx newResults hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setResults {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setResults op' ctx newResults hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setResults {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setResults op' ctx newResults hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setOperands -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setOperands op' ctx newOperands hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setOperands op' ctx newOperands hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setOperands op' ctx newOperands hop') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setOperands op' ctx newOperands hop') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setOperands {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setOperands op' ctx newOperands hop') =
    operation.getAttributes! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setOperands op' ctx newOperands hop') =
    if opOperand.op = op' then
      newOperands[opOperand.index]!.nextUse
    else
      opOperand.getNextUse! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setOperands op' ctx newOperands hop') =
    if opOperand.op = op' then
      newOperands[opOperand.index]!.back
    else
      opOperand.getBack! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setOperands op' ctx newOperands hop') =
    if opOperand.op = op' then
      newOperands[opOperand.index]!.owner
    else
      opOperand.getOwner! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setOperands op' ctx newOperands hop') =
    if opOperand.op = op' then
      newOperands[opOperand.index]!.value
    else
      opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setOperands op' ctx newOperands hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setOperands op' ctx newOperands hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setOperands op' ctx newOperands hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setOperands {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setOperands op' ctx newOperands hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setOperands {block : BlockPtr} :
    block.getParent! (OperationPtr.setOperands op' ctx newOperands hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setOperands {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setOperands op' ctx newOperands hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setOperands {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setOperands op' ctx newOperands hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setOperands {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setOperands op' ctx newOperands hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setOperands {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setOperands op' ctx newOperands hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setOperands {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setOperands op' ctx newOperands hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setOperands op' ctx newOperands hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setOperands {region : RegionPtr} :
    region.getParent! (OperationPtr.setOperands op' ctx newOperands hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setOperands {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setOperands op' ctx newOperands hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setOperands {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setOperands op' ctx newOperands hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.setBlockOperands -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getParent! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_setBlockOperands {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_setBlockOperands {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opOperand.getValue! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    if blockOperand.op = op' then
      newOperands[blockOperand.index]!.nextUse
    else
      blockOperand.getNextUse! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    if blockOperand.op = op' then
      newOperands[blockOperand.index]!.back
    else
      blockOperand.getBack! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    if blockOperand.op = op' then
      newOperands[blockOperand.index]!.owner
    else
      blockOperand.getOwner! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_setBlockOperands {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    if blockOperand.op = op' then
      newOperands[blockOperand.index]!.value
    else
      blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_setBlockOperands {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getParent! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getLastOp! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_setBlockOperands {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_setBlockOperands {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.getParent! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_setBlockOperands {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.setBlockOperands op' ctx newOperands hop') =
    region.getLastBlock! ctx := by
  grind

/- OpOperandPtr.setNextUse -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getRegions! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    operation.getAttributes! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    if opOperand = opOperand' then
      newNextUse
    else
      opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setNextUse {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setNextUse {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setNextUse opOperand' ctx newNextUse hopOperand') =
    region.getLastBlock! ctx := by
  grind

/- OpOperandPtr.setBack -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getRegions! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setBack {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    if opOperand = opOperand' then
      newBack
    else
      opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setBack {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setBack {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setBack {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setBack {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setBack opOperand' ctx newBack hopOperand') =
    region.getLastBlock! ctx := by
  grind

/- OpOperandPtr.setOwner -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getRegions! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setOwner {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opOperand.getBack! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    if opOperand = opOperand' then
      newOwner
    else
      opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setOwner {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setOwner {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setOwner opOperand' ctx newOwner hopOperand') =
    region.getLastBlock! ctx := by
  grind

/- OpOperandPtr.setValue -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getParent! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getRegions! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtr_setValue {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opOperand.getOwner! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.getValue!_OpOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    if opOperand = opOperand' then
      newValue
    else
      opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getParent! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getLastOp! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtr_setValue {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtr_setValue {region : RegionPtr} :
    region.getParent! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtr_setValue {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtr_setValue {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtr.setValue opOperand' ctx newValue hopOperand') =
    region.getLastBlock! ctx := by
  grind

/- BlockOperandPtr.setNextUse -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getRegions! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setNextUse {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setNextUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opOperand.getValue! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    if blockOperand = blockOperand' then
      newNextUse
    else
      blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setNextUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtr_setNextUse {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setNextUse {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setNextUse {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setNextUse {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setNextUse blockOperand' ctx newNextUse hblockOperand') =
    region.getLastBlock! ctx := by
  grind

/- BlockOperandPtr.setBack -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getRegions! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setBack {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setBack {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    if blockOperand = blockOperand' then
      newBack
    else
      blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setBack {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtr_setBack {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setBack {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setBack {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setBack {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setBack blockOperand' ctx newBack hblockOperand') =
    region.getLastBlock! ctx := by
  grind

/- BlockOperandPtr.setOwner -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getRegions! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setOwner {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockOperand.getBack! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    if blockOperand = blockOperand' then
      newOwner
    else
      blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtr_setOwner {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setOwner {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setOwner {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setOwner blockOperand' ctx newOwner hblockOperand') =
    region.getLastBlock! ctx := by
  grind

/- BlockOperandPtr.setValue -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getRegions! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtr_setValue {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtr_setValue {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockOperand.getOwner! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtr_setValue {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    if blockOperand = blockOperand' then
      newValue
    else
      blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtr_setValue {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getParent! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtr_setValue {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtr_setValue {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.getParent! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtr_setValue {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtr.setValue blockOperand' ctx newValue hblockOperand') =
    region.getLastBlock! ctx := by
  grind

/- OpResultPtr.setType -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getNextOp! (OpResultPtr.setType opResult' ctx newType hopResult') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getPrevOp! (OpResultPtr.setType opResult' ctx newType hopResult') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getParent! (OpResultPtr.setType opResult' ctx newType hopResult') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getRegions! (OpResultPtr.setType opResult' ctx newType hopResult') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpResultPtr_setType {operation : OperationPtr} :
    operation.getAttributes! (OpResultPtr.setType opResult' ctx newType hopResult') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpResultPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpResultPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockOperand.getValue! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getType!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getType! (OpResultPtr.setType opResult' ctx newType hopResult') =
    if opResult = opResult' then
      newType
    else
      opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getOwner! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpResultPtr_setType {opResult : OpResultPtr} :
    opResult.getIndex! (OpResultPtr.setType opResult' ctx newType hopResult') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpResultPtr_setType {block : BlockPtr} :
    block.getParent! (OpResultPtr.setType opResult' ctx newType hopResult') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpResultPtr_setType {block : BlockPtr} :
    block.getFirstUse! (OpResultPtr.setType opResult' ctx newType hopResult') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpResultPtr_setType {block : BlockPtr} :
    block.getFirstOp! (OpResultPtr.setType opResult' ctx newType hopResult') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpResultPtr_setType {block : BlockPtr} :
    block.getLastOp! (OpResultPtr.setType opResult' ctx newType hopResult') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpResultPtr_setType {block : BlockPtr} :
    block.getNextBlock! (OpResultPtr.setType opResult' ctx newType hopResult') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpResultPtr_setType {block : BlockPtr} :
    block.getPrevBlock! (OpResultPtr.setType opResult' ctx newType hopResult') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpResultPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpResultPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpResultPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpResultPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpResultPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpResultPtr.setType opResult' ctx newType hopResult') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpResultPtr_setType {region : RegionPtr} :
    region.getParent! (OpResultPtr.setType opResult' ctx newType hopResult') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpResultPtr_setType {region : RegionPtr} :
    region.getFirstBlock! (OpResultPtr.setType opResult' ctx newType hopResult') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpResultPtr_setType {region : RegionPtr} :
    region.getLastBlock! (OpResultPtr.setType opResult' ctx newType hopResult') =
    region.getLastBlock! ctx := by
  grind

/- OpResultPtr.setFirstUse -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getRegions! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpResultPtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpResultPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpResultPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opResult.getType! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    if opResult = opResult' then
      newFirstUse
    else
      opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpResultPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getParent! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpResultPtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpResultPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpResultPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpResultPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpResultPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpResultPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.getParent! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpResultPtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (OpResultPtr.setFirstUse opResult' ctx newFirstUse hopResult') =
    region.getLastBlock! ctx := by
  grind

/- OpResultPtr.setOwner -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpResultPtr_setOwner {operation : OperationPtr} :
    operation.getNextOp! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpResultPtr_setOwner {operation : OperationPtr} :
    operation.getPrevOp! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OpResultPtr_setOwner {operation : OperationPtr} :
    operation.getParent! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_OpResultPtr_setOwner {operation : OperationPtr} :
    operation.getRegions! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpResultPtr_setOwner {operation : OperationPtr} :
    operation.getAttributes! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_OpResultPtr_setOwner {operation : OperationPtr} :
    operation.getProperties! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OpResultPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpResultPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpResultPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpResultPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpResultPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpResultPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpResultPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpResultPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OpResultPtr_setOwner {opResult : OpResultPtr} :
    opResult.getType! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OpResultPtr_setOwner {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opResult.getFirstUse! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getOwner!_OpResultPtr_setOwner {opResult : OpResultPtr} :
    opResult.getOwner! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    if opResult = opResult' then
      newOwner
    else
      opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpResultPtr_setOwner {block : BlockPtr} :
    block.getParent! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpResultPtr_setOwner {block : BlockPtr} :
    block.getFirstUse! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpResultPtr_setOwner {block : BlockPtr} :
    block.getFirstOp! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpResultPtr_setOwner {block : BlockPtr} :
    block.getLastOp! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpResultPtr_setOwner {block : BlockPtr} :
    block.getNextBlock! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpResultPtr_setOwner {block : BlockPtr} :
    block.getPrevBlock! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpResultPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OpResultPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpResultPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpResultPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpResultPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpResultPtr_setOwner {value : ValuePtr} :
    value.getType! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_OpResultPtr_setOwner {value : ValuePtr} :
    value.getFirstUse! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OpResultPtr_setOwner {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    opOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpResultPtr_setOwner {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OpResultPtr_setOwner {region : RegionPtr} :
    region.getParent! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpResultPtr_setOwner {region : RegionPtr} :
    region.getFirstBlock! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpResultPtr_setOwner {region : RegionPtr} :
    region.getLastBlock! (OpResultPtr.setOwner opResult' ctx newOwner hopResult') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setParent -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setParent {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setParent block' ctx newParent hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setParent block' ctx newParent hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setParent block' ctx newParent hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setParent {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setParent block' ctx newParent hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =]
theorem BlockPtr.getParent!_BlockPtr_setParent {block : BlockPtr} :
    block.getParent! (BlockPtr.setParent block' ctx newParent hblock') =
    if block = block' then
      newParent
    else
      block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setParent {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setParent {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setParent {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setParent {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setParent {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setParent block' ctx newParent hblock') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setParent block' ctx newParent hblock') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setParent block' ctx newParent hblock') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setParent block' ctx newParent hblock') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setParent block' ctx newParent hblock') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setParent {region : RegionPtr} :
    region.getParent! (BlockPtr.setParent block' ctx newParent hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setParent {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setParent {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setParent block' ctx newParent hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setFirstUse -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getParent! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getParent! ctx := by
  grind

@[grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    if block = block' then
      newFirstUse
    else
      block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.getParent! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setFirstUse block' ctx newFirstUse hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setFirstOp -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setFirstOp {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setFirstOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setFirstOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setFirstOp {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getParent! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getFirstUse! ctx := by
  grind

@[grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    if block = block' then
      newFirstOp
    else
      block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setFirstOp {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setFirstOp {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setFirstOp {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setFirstOp {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setFirstOp {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setFirstOp {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.getParent! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setFirstOp {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setFirstOp block' ctx newFirstOp hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setLastOp -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setLastOp {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setLastOp {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setLastOp {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setLastOp {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getParent! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getFirstOp! ctx := by
  grind

@[grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    if block = block' then
      newLastOp
    else
      block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setLastOp {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setLastOp {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setLastOp {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setLastOp {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setLastOp {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setLastOp {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setLastOp {region : RegionPtr} :
    region.getParent! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setLastOp {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setLastOp {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setLastOp block' ctx newLastOp hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setNextBlock -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setNextBlock {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setNextBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setNextBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setNextBlock {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getParent! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    block.getLastOp! ctx := by
  grind

@[grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    if block = block' then
      newNext
    else
      block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setNextBlock {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setNextBlock {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setNextBlock {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setNextBlock {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setNextBlock {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setNextBlock {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.getParent! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setNextBlock {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setNextBlock block' ctx newNext hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setPrevBlock -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setPrevBlock {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setPrevBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setPrevBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setPrevBlock {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getParent! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    block.getNextBlock! ctx := by
  grind

@[grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setPrevBlock {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    if block = block' then
      newPrev
    else
      block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setPrevBlock {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setPrevBlock {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setPrevBlock {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setPrevBlock {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setPrevBlock {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.getParent! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setPrevBlock {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setPrevBlock block' ctx newPrev hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.setArguments -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getParent! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_setArguments {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.setArguments block' ctx newArguments hblock') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_setArguments {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_setArguments {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.setArguments block' ctx newArguments hblock') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_setArguments {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.setArguments block' ctx newArguments hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_setArguments {block : BlockPtr} :
    block.getParent! (BlockPtr.setArguments block' ctx newArguments hblock') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_setArguments {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_setArguments {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.setArguments block' ctx newArguments hblock') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_setArguments {block : BlockPtr} :
    block.getLastOp! (BlockPtr.setArguments block' ctx newArguments hblock') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_setArguments {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.setArguments block' ctx newArguments hblock') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_setArguments {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.setArguments block' ctx newArguments hblock') =
    block.getPrevBlock! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then
      newArguments[blockArg.index]!.type
    else
      blockArg.getType! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then
      newArguments[blockArg.index]!.firstUse
    else
      blockArg.getFirstUse! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then
      newArguments[blockArg.index]!.index
    else
      blockArg.getIndex! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then
      newArguments[blockArg.index]!.loc
    else
      blockArg.getLoc! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_setArguments {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.setArguments block' ctx newArguments hblock') =
    if blockArg.block = block' then
      newArguments[blockArg.index]!.owner
    else
      blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_setArguments {region : RegionPtr} :
    region.getParent! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_setArguments {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_setArguments {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.setArguments block' ctx newArguments hblock') =
    region.getLastBlock! ctx := by
  grind

/- BlockArgumentPtr.setType -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getRegions! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setType {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockArgumentPtr_setType {opResult : OpResultPtr} :
    opResult.getIndex! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setType {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    block.getPrevBlock! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    if blockArg = blockArg' then
      newType
    else
      blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setType {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setType blockArg' ctx newType hblockArg') =
    region.getLastBlock! ctx := by
  grind

/- BlockArgumentPtr.setFirstUse -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getRegions! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockArgumentPtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockArg.getType! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    if blockArg = blockArg' then
      newFirstUse
    else
      blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setFirstUse blockArg' ctx newFirstUse hblockArg') =
    region.getLastBlock! ctx := by
  grind

/- BlockArgumentPtr.setIndex -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setIndex {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setIndex {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setIndex {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockArgumentPtr_setIndex {operation : OperationPtr} :
    operation.getRegions! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setIndex {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockArgumentPtr_setIndex {operation : OperationPtr} :
    operation.getProperties! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setIndex {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setIndex {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setIndex {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setIndex {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setIndex {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setIndex {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setIndex {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setIndex {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setIndex {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setIndex {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setIndex {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setIndex {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setIndex {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setIndex {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setIndex {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setIndex {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setIndex {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setIndex {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setIndex {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockArg.getFirstUse! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setIndex {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    if blockArg = blockArg' then
      newIndex
    else
      blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setIndex {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setIndex {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockArgumentPtr_setIndex {value : ValuePtr} :
    value.getType! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockArgumentPtr_setIndex {value : ValuePtr} :
    value.getFirstUse! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockArgumentPtr_setIndex {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    opOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockArgumentPtr_setIndex {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setIndex {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setIndex {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setIndex {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setIndex blockArg' ctx newIndex hblockArg') =
    region.getLastBlock! ctx := by
  grind

/- BlockArgumentPtr.setLoc -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getRegions! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setLoc {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setLoc {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setLoc {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockArgumentPtr_setLoc {opResult : OpResultPtr} :
    opResult.getIndex! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setLoc {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setLoc {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setLoc {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setLoc {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockArg.getIndex! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setLoc {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    if blockArg = blockArg' then
      newLoc
    else
      blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setLoc {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setLoc {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setLoc blockArg' ctx newLoc hblockArg') =
    region.getLastBlock! ctx := by
  grind

/- BlockArgumentPtr.setOwner -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockArgumentPtr_setOwner {operation : OperationPtr} :
    operation.getNextOp! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockArgumentPtr_setOwner {operation : OperationPtr} :
    operation.getPrevOp! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_BlockArgumentPtr_setOwner {operation : OperationPtr} :
    operation.getParent! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockArgumentPtr_setOwner {operation : OperationPtr} :
    operation.getRegions! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockArgumentPtr_setOwner {operation : OperationPtr} :
    operation.getAttributes! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_BlockArgumentPtr_setOwner {operation : OperationPtr} :
    operation.getProperties! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockArgumentPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockArgumentPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockArgumentPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockArgumentPtr_setOwner {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockArgumentPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockArgumentPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockArgumentPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockArgumentPtr_setOwner {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_BlockArgumentPtr_setOwner {opResult : OpResultPtr} :
    opResult.getType! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockArgumentPtr_setOwner {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockArgumentPtr_setOwner {opResult : OpResultPtr} :
    opResult.getOwner! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockArgumentPtr_setOwner {block : BlockPtr} :
    block.getParent! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockArgumentPtr_setOwner {block : BlockPtr} :
    block.getFirstUse! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockArgumentPtr_setOwner {block : BlockPtr} :
    block.getFirstOp! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockArgumentPtr_setOwner {block : BlockPtr} :
    block.getLastOp! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockArgumentPtr_setOwner {block : BlockPtr} :
    block.getNextBlock! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockArgumentPtr_setOwner {block : BlockPtr} :
    block.getPrevBlock! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockArgumentPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockArgumentPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockArgumentPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockArgumentPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockArg.getLoc! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getOwner!_BlockArgumentPtr_setOwner {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    if blockArg = blockArg' then
      newOwner
    else
      blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_BlockArgumentPtr_setOwner {value : ValuePtr} :
    value.getType! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockArgumentPtr_setOwner {value : ValuePtr} :
    value.getFirstUse! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_BlockArgumentPtr_setOwner {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    opOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_BlockArgumentPtr_setOwner {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_BlockArgumentPtr_setOwner {region : RegionPtr} :
    region.getParent! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockArgumentPtr_setOwner {region : RegionPtr} :
    region.getFirstBlock! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockArgumentPtr_setOwner {region : RegionPtr} :
    region.getLastBlock! (BlockArgumentPtr.setOwner blockArg' ctx newOwner hblockArg') =
    region.getLastBlock! ctx := by
  grind

/- ValuePtr.setType -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_ValuePtr_setType {operation : OperationPtr} :
    operation.getNextOp! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_ValuePtr_setType {operation : OperationPtr} :
    operation.getPrevOp! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_ValuePtr_setType {operation : OperationPtr} :
    operation.getParent! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_ValuePtr_setType {operation : OperationPtr} :
    operation.getRegions! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_ValuePtr_setType {operation : OperationPtr} :
    operation.getAttributes! (ValuePtr.setType value' ctx newType hvalue') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getBack! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_ValuePtr_setType {opOperand : OpOperandPtr} :
    opOperand.getValue! (ValuePtr.setType value' ctx newType hvalue') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_ValuePtr_setType {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (ValuePtr.setType value' ctx newType hvalue') =
    blockOperand.getValue! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getType!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getType! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = .opResult opResult then
      newType
    else
      opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_ValuePtr_setType {opResult : OpResultPtr} :
    opResult.getIndex! (ValuePtr.setType value' ctx newType hvalue') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_ValuePtr_setType {block : BlockPtr} :
    block.getParent! (ValuePtr.setType value' ctx newType hvalue') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_ValuePtr_setType {block : BlockPtr} :
    block.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_ValuePtr_setType {block : BlockPtr} :
    block.getFirstOp! (ValuePtr.setType value' ctx newType hvalue') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_ValuePtr_setType {block : BlockPtr} :
    block.getLastOp! (ValuePtr.setType value' ctx newType hvalue') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_ValuePtr_setType {block : BlockPtr} :
    block.getNextBlock! (ValuePtr.setType value' ctx newType hvalue') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_ValuePtr_setType {block : BlockPtr} :
    block.getPrevBlock! (ValuePtr.setType value' ctx newType hvalue') =
    block.getPrevBlock! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getType!_ValuePtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getType! (ValuePtr.setType value' ctx newType hvalue') =
    if value' = .blockArgument blockArg then
      newType
    else
      blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_ValuePtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (ValuePtr.setType value' ctx newType hvalue') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_ValuePtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (ValuePtr.setType value' ctx newType hvalue') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_ValuePtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (ValuePtr.setType value' ctx newType hvalue') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_ValuePtr_setType {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (ValuePtr.setType value' ctx newType hvalue') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_ValuePtr_setType {region : RegionPtr} :
    region.getParent! (ValuePtr.setType value' ctx newType hvalue') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_ValuePtr_setType {region : RegionPtr} :
    region.getFirstBlock! (ValuePtr.setType value' ctx newType hvalue') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_ValuePtr_setType {region : RegionPtr} :
    region.getLastBlock! (ValuePtr.setType value' ctx newType hvalue') =
    region.getLastBlock! ctx := by
  grind

/- ValuePtr.setFirstUse -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getNextOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getPrevOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getParent! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getRegions! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_ValuePtr_setFirstUse {operation : OperationPtr} :
    operation.getAttributes! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getBack! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_ValuePtr_setFirstUse {opOperand : OpOperandPtr} :
    opOperand.getValue! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_ValuePtr_setFirstUse {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getType! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opResult.getType! ctx := by
  grind

@[grind =]
theorem OpResultPtr.getFirstUse!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = .opResult opResult then
      newFirstUse
    else
      opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_ValuePtr_setFirstUse {opResult : OpResultPtr} :
    opResult.getIndex! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getParent! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getFirstOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getLastOp! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getNextBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_ValuePtr_setFirstUse {block : BlockPtr} :
    block.getPrevBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_ValuePtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getType! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockArg.getType! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_ValuePtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    if value' = .blockArgument blockArg then
      newFirstUse
    else
      blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_ValuePtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_ValuePtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_ValuePtr_setFirstUse {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.getParent! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.getFirstBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_ValuePtr_setFirstUse {region : RegionPtr} :
    region.getLastBlock! (ValuePtr.setFirstUse value' ctx newFirstUse hvalue') =
    region.getLastBlock! ctx := by
  grind

/- OpOperandPtrPtr.set -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNextOp! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    operation.getNextOp! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getPrevOp! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    operation.getPrevOp! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getParent!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getParent! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    operation.getParent! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getRegions!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getRegions! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    operation.getRegions! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getAttributes!_OpOperandPtrPtr_set {operation : OperationPtr} :
    operation.getAttributes! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    operation.getAttributes! ctx := by
  grind [cases OpOperandPtrPtr]

@[grind =]
theorem OpOperandPtr.getNextUse!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    if opOperandPtr' = .operandNextUse opOperand then
      newValue
    else
      opOperand.getNextUse! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getBack!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getBack! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    opOperand.getBack! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    opOperand.getOwner! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getValue!_OpOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getValue! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    opOperand.getValue! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockOperand.getNextUse! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockOperand.getBack! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockOperand.getOwner! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OpOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockOperand.getValue! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getType!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getType! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    opResult.getType! ctx := by
  grind [cases OpOperandPtrPtr]

@[grind =]
theorem OpResultPtr.getFirstUse!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getFirstUse! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    if opOperandPtr' = .valueFirstUse (.opResult opResult) then
      newValue
    else
      opResult.getFirstUse! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getOwner!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getOwner! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    opResult.getOwner! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getIndex!_OpOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getIndex! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getParent! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    block.getParent! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstUse! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    block.getFirstUse! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstOp! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    block.getFirstOp! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getLastOp!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getLastOp! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    block.getLastOp! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getNextBlock! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    block.getNextBlock! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OpOperandPtrPtr_set {block : BlockPtr} :
    block.getPrevBlock! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    block.getPrevBlock! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OpOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockArg.getType! ctx := by
  grind [cases OpOperandPtrPtr]

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_OpOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    if opOperandPtr' = .valueFirstUse (.blockArgument blockArg) then
      newValue
    else
      blockArg.getFirstUse! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OpOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockArg.getIndex! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OpOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockArg.getLoc! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OpOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    blockArg.getOwner! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem RegionPtr.getParent!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.getParent! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    region.getParent! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.getFirstBlock! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    region.getFirstBlock! ctx := by
  grind [cases OpOperandPtrPtr]

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OpOperandPtrPtr_set {region : RegionPtr} :
    region.getLastBlock! (OpOperandPtrPtr.set opOperandPtr' ctx newValue hopOperandPtr') =
    region.getLastBlock! ctx := by
  grind [cases OpOperandPtrPtr]

/- BlockOperandPtrPtr.set -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getNextOp! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    operation.getNextOp! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getPrevOp! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    operation.getPrevOp! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getParent!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getParent! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    operation.getParent! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getRegions! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    operation.getRegions! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockOperandPtrPtr_set {operation : OperationPtr} :
    operation.getAttributes! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    operation.getAttributes! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opOperand.getNextUse! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opOperand.getBack! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opOperand.getOwner! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockOperandPtrPtr_set {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opOperand.getValue! ctx := by
  grind [cases BlockOperandPtrPtr]

@[grind =]
theorem BlockOperandPtr.getNextUse!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    if blockOperandPtr' = .blockOperandNextUse blockOperand then
      newValue
    else
      blockOperand.getNextUse! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockOperand.getBack! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockOperand.getOwner! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockOperandPtrPtr_set {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockOperand.getValue! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getType!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getType! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opResult.getType! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opResult.getFirstUse! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getOwner! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opResult.getOwner! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockOperandPtrPtr_set {opResult : OpResultPtr} :
    opResult.getIndex! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getParent! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    block.getParent! ctx := by
  grind [cases BlockOperandPtrPtr]

@[grind =]
theorem BlockPtr.getFirstUse!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstUse! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    if blockOperandPtr' = .blockFirstUse block then
      newValue
    else
      block.getFirstUse! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getFirstOp! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    block.getFirstOp! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getLastOp! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    block.getLastOp! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getNextBlock! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    block.getNextBlock! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockOperandPtrPtr_set {block : BlockPtr} :
    block.getPrevBlock! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    block.getPrevBlock! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getType!_BlockOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockArg.getType! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockArg.getFirstUse! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_BlockOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockArg.getIndex! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_BlockOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockArg.getLoc! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_BlockOperandPtrPtr_set {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    blockArg.getOwner! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem RegionPtr.getParent!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.getParent! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    region.getParent! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.getFirstBlock! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    region.getFirstBlock! ctx := by
  grind [cases BlockOperandPtrPtr]

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockOperandPtrPtr_set {region : RegionPtr} :
    region.getLastBlock! (BlockOperandPtrPtr.set blockOperandPtr' ctx newValue hblockOperandPtr') =
    region.getLastBlock! ctx := by
  grind [cases BlockOperandPtrPtr]

/- RegionPtr.setParent -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getParent! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getRegions! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_setParent {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.setParent region' ctx newParent hregion') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_setParent {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.setParent region' ctx newParent hregion') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_setParent {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.setParent region' ctx newParent hregion') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_setParent {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.setParent region' ctx newParent hregion') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_setParent {block : BlockPtr} :
    block.getParent! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_setParent {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_setParent {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_setParent {block : BlockPtr} :
    block.getLastOp! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_setParent {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_setParent {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getType! (RegionPtr.setParent region' ctx newParent hregion') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (RegionPtr.setParent region' ctx newParent hregion') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (RegionPtr.setParent region' ctx newParent hregion') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (RegionPtr.setParent region' ctx newParent hregion') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_setParent {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (RegionPtr.setParent region' ctx newParent hregion') =
    blockArg.getOwner! ctx := by
  grind

@[grind =]
theorem RegionPtr.getParent!_RegionPtr_setParent {region : RegionPtr} :
    region.getParent! (RegionPtr.setParent region' ctx newParent hregion') =
    if region = region' then
      newParent
    else
      region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_setParent {region : RegionPtr} :
    region.getFirstBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_setParent {region : RegionPtr} :
    region.getLastBlock! (RegionPtr.setParent region' ctx newParent hregion') =
    region.getLastBlock! ctx := by
  grind

/- RegionPtr.setFirstBlock -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getParent! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getRegions! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_setFirstBlock {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_setFirstBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_setFirstBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_setFirstBlock {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getParent! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getLastOp! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_setFirstBlock {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_setFirstBlock {blockArg : BlockArgumentPtr} :
    blockArg.getType! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_setFirstBlock {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_setFirstBlock {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_setFirstBlock {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_setFirstBlock {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.getParent! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    region.getParent! ctx := by
  grind

@[grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.getFirstBlock! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    if region = region' then
      newFirstBlock
    else
      region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_setFirstBlock {region : RegionPtr} :
    region.getLastBlock! (RegionPtr.setFirstBlock region' ctx newFirstBlock hregion') =
    region.getLastBlock! ctx := by
  grind

/- RegionPtr.setLastBlock -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getNextOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getPrevOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getParent! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getParent! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegions!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getRegions! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_RegionPtr_setLastBlock {operation : OperationPtr} :
    operation.getAttributes! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getBack! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_RegionPtr_setLastBlock {opOperand : OpOperandPtr} :
    opOperand.getValue! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_RegionPtr_setLastBlock {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getType! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_RegionPtr_setLastBlock {opResult : OpResultPtr} :
    opResult.getIndex! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getParent! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getFirstOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getLastOp! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getNextBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_RegionPtr_setLastBlock {block : BlockPtr} :
    block.getPrevBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_RegionPtr_setLastBlock {blockArg : BlockArgumentPtr} :
    blockArg.getType! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_setLastBlock {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_RegionPtr_setLastBlock {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_RegionPtr_setLastBlock {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_RegionPtr_setLastBlock {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.getParent! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.getFirstBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    region.getFirstBlock! ctx := by
  grind

@[grind =]
theorem RegionPtr.getLastBlock!_RegionPtr_setLastBlock {region : RegionPtr} :
    region.getLastBlock! (RegionPtr.setLastBlock region' ctx newLastBlock hregion') =
    if region = region' then
      newLastBlock
    else
      region.getLastBlock! ctx := by
  grind

/- OperationPtr.allocEmpty -/

@[grind =>]
theorem OperationPtr.getNextOp!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getNextOp! ctx' =
    if operation = op' then
      none
    else
      operation.getNextOp! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[grind =>]
theorem OperationPtr.getPrevOp!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getPrevOp! ctx' =
    if operation = op' then
      none
    else
      operation.getPrevOp! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[grind =>]
theorem OperationPtr.getParent!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getParent! ctx' =
    if operation = op' then
      none
    else
      operation.getParent! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[grind =>]
theorem OperationPtr.getRegions!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getRegions! ctx' =
    if operation = op' then
      #[]
    else
      operation.getRegions! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[grind =>]
theorem OperationPtr.getAttributes!_OperationPtr_allocEmpty {operation : OperationPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    operation.getAttributes! ctx' =
    if operation = op' then
      DictionaryAttr.empty
    else
      operation.getAttributes! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpOperandPtr.getNextUse!_OperationPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpOperandPtr.getBack!_OperationPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpOperandPtr.getOwner!_OperationPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpOperandPtr.getValue!_OperationPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getNextUse!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getBack!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getOwner!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getValue!_OperationPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpResultPtr.getType!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpResultPtr.getFirstUse!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpResultPtr.getOwner!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem OpResultPtr.getIndex!_OperationPtr_allocEmpty {opResult : OpResultPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind [Operation.default_results_eq]

@[simp, grind =>]
theorem BlockPtr.getParent!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getParent! ctx' =
    block.getParent! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockPtr.getFirstUse!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getFirstUse! ctx' =
    block.getFirstUse! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockPtr.getFirstOp!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getFirstOp! ctx' =
    block.getFirstOp! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockPtr.getLastOp!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getLastOp! ctx' =
    block.getLastOp! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockPtr.getNextBlock!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getNextBlock! ctx' =
    block.getNextBlock! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockPtr.getPrevBlock!_OperationPtr_allocEmpty {block : BlockPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    block.getPrevBlock! ctx' =
    block.getPrevBlock! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getType!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getIndex!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getOwner!_OperationPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem RegionPtr.getParent!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.getParent! ctx' =
    region.getParent! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem RegionPtr.getFirstBlock!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.getFirstBlock! ctx' =
    region.getFirstBlock! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

@[simp, grind =>]
theorem RegionPtr.getLastBlock!_OperationPtr_allocEmpty {region : RegionPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    region.getLastBlock! ctx' =
    region.getLastBlock! ctx := by
  grind [Operation.default_results_eq, Operation.default_operands_eq, Operation.default_blockOperands_eq]

/- OperationPtr.dealloc -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc op' ctx hop') →
    operation.getNextOp! (OperationPtr.dealloc op' ctx hop') =
    operation.getNextOp! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc op' ctx hop') →
    operation.getPrevOp! (OperationPtr.dealloc op' ctx hop') =
    operation.getPrevOp! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc op' ctx hop') →
    operation.getParent! (OperationPtr.dealloc op' ctx hop') =
    operation.getParent! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc op' ctx hop') →
    operation.getRegions! (OperationPtr.dealloc op' ctx hop') =
    operation.getRegions! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc op' ctx hop') →
    operation.getAttributes! (OperationPtr.dealloc op' ctx hop') =
    operation.getAttributes! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opOperand.getNextUse! (OperationPtr.dealloc op' ctx hop') =
    opOperand.getNextUse! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opOperand.getBack! (OperationPtr.dealloc op' ctx hop') =
    opOperand.getBack! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opOperand.getOwner! (OperationPtr.dealloc op' ctx hop') =
    opOperand.getOwner! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_dealloc {opOperand : OpOperandPtr} :
    opOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opOperand.getValue! (OperationPtr.dealloc op' ctx hop') =
    opOperand.getValue! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    blockOperand.getNextUse! (OperationPtr.dealloc op' ctx hop') =
    blockOperand.getNextUse! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    blockOperand.getBack! (OperationPtr.dealloc op' ctx hop') =
    blockOperand.getBack! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    blockOperand.getOwner! (OperationPtr.dealloc op' ctx hop') =
    blockOperand.getOwner! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_dealloc {blockOperand : BlockOperandPtr} :
    blockOperand.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    blockOperand.getValue! (OperationPtr.dealloc op' ctx hop') =
    blockOperand.getValue! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opResult.getType! (OperationPtr.dealloc op' ctx hop') =
    opResult.getType! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opResult.getFirstUse! (OperationPtr.dealloc op' ctx hop') =
    opResult.getFirstUse! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opResult.getOwner! (OperationPtr.dealloc op' ctx hop') =
    opResult.getOwner! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_dealloc {opResult : OpResultPtr} :
    opResult.op.InBounds (OperationPtr.dealloc op' ctx hop') →
    opResult.getIndex! (OperationPtr.dealloc op' ctx hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_dealloc {block : BlockPtr} :
    block.getParent! (OperationPtr.dealloc op' ctx hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_dealloc {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.dealloc op' ctx hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_dealloc {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.dealloc op' ctx hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_dealloc {block : BlockPtr} :
    block.getLastOp! (OperationPtr.dealloc op' ctx hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_dealloc {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.dealloc op' ctx hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_dealloc {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.dealloc op' ctx hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.dealloc op' ctx hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.dealloc op' ctx hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.dealloc op' ctx hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.dealloc op' ctx hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_dealloc {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.dealloc op' ctx hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_dealloc {region : RegionPtr} :
    region.getParent! (OperationPtr.dealloc op' ctx hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_dealloc {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.dealloc op' ctx hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_dealloc {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.dealloc op' ctx hop') =
    region.getLastBlock! ctx := by
  grind

/- OperationPtr.pushOperand -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushOperand op' ctx newOperand hop') =
    operation.getNextOp! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushOperand op' ctx newOperand hop') =
    operation.getPrevOp! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushOperand op' ctx newOperand hop') =
    operation.getParent! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.pushOperand op' ctx newOperand hop') =
    operation.getRegions! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushOperand {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushOperand op' ctx newOperand hop') =
    operation.getAttributes! ctx := by
  grind [OperationPtr.getOpOperand]

@[grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushOperand {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushOperand op' ctx newOperand hop') =
    if opOperand = op'.nextOperand ctx then
      newOperand.nextUse
    else
      opOperand.getNextUse! ctx := by
  grind [OperationPtr.getOpOperand]

@[grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushOperand {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushOperand op' ctx newOperand hop') =
    if opOperand = op'.nextOperand ctx then
      newOperand.back
    else
      opOperand.getBack! ctx := by
  grind [OperationPtr.getOpOperand]

@[grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushOperand {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushOperand op' ctx newOperand hop') =
    if opOperand = op'.nextOperand ctx then
      newOperand.owner
    else
      opOperand.getOwner! ctx := by
  grind [OperationPtr.getOpOperand]

@[grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushOperand {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushOperand op' ctx newOperand hop') =
    if opOperand = op'.nextOperand ctx then
      newOperand.value
    else
      opOperand.getValue! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockOperand.getNextUse! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockOperand.getBack! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockOperand.getOwner! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockOperand.getValue! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushOperand op' ctx newOperand hop') =
    opResult.getType! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushOperand op' ctx newOperand hop') =
    opResult.getFirstUse! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushOperand op' ctx newOperand hop') =
    opResult.getOwner! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_pushOperand {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushOperand op' ctx newOperand hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getParent! (OperationPtr.pushOperand op' ctx newOperand hop') =
    block.getParent! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushOperand op' ctx newOperand hop') =
    block.getFirstUse! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushOperand op' ctx newOperand hop') =
    block.getFirstOp! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushOperand op' ctx newOperand hop') =
    block.getLastOp! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushOperand op' ctx newOperand hop') =
    block.getNextBlock! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushOperand {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushOperand op' ctx newOperand hop') =
    block.getPrevBlock! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockArg.getType! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockArg.getFirstUse! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockArg.getIndex! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockArg.getLoc! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushOperand op' ctx newOperand hop') =
    blockArg.getOwner! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushOperand {region : RegionPtr} :
    region.getParent! (OperationPtr.pushOperand op' ctx newOperand hop') =
    region.getParent! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushOperand {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushOperand op' ctx newOperand hop') =
    region.getFirstBlock! ctx := by
  grind [OperationPtr.getOpOperand]

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushOperand {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushOperand op' ctx newOperand hop') =
    region.getLastBlock! ctx := by
  grind [OperationPtr.getOpOperand]

/- OperationPtr.pushBlockOperand -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    operation.getNextOp! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    operation.getPrevOp! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    operation.getParent! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    operation.getRegions! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushBlockOperand {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    operation.getAttributes! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opOperand.getNextUse! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opOperand.getBack! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opOperand.getOwner! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushBlockOperand {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opOperand.getValue! ctx := by
  grind [OperationPtr.getBlockOperand]

@[grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    if blockOperand = op'.nextBlockOperand ctx then
      newOperand.nextUse
    else
      blockOperand.getNextUse! ctx := by
  grind [OperationPtr.getBlockOperand]

@[grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    if blockOperand = op'.nextBlockOperand ctx then
      newOperand.back
    else
      blockOperand.getBack! ctx := by
  grind [OperationPtr.getBlockOperand]

@[grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    if blockOperand = op'.nextBlockOperand ctx then
      newOperand.owner
    else
      blockOperand.getOwner! ctx := by
  grind [OperationPtr.getBlockOperand]

@[grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushBlockOperand {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    if blockOperand = op'.nextBlockOperand ctx then
      newOperand.value
    else
      blockOperand.getValue! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opResult.getType! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opResult.getFirstUse! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opResult.getOwner! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_pushBlockOperand {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getParent! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    block.getParent! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    block.getFirstUse! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    block.getFirstOp! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    block.getLastOp! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    block.getNextBlock! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushBlockOperand {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    block.getPrevBlock! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    blockArg.getType! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    blockArg.getFirstUse! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    blockArg.getIndex! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    blockArg.getLoc! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushBlockOperand {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    blockArg.getOwner! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.getParent! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    region.getParent! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    region.getFirstBlock! ctx := by
  grind [OperationPtr.getBlockOperand]

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushBlockOperand {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushBlockOperand op' ctx newOperand hop') =
    region.getLastBlock! ctx := by
  grind [OperationPtr.getBlockOperand]

/- OperationPtr.pushResult -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushResult op' ctx newResult hop') =
    operation.getNextOp! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushResult op' ctx newResult hop') =
    operation.getPrevOp! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushResult op' ctx newResult hop') =
    operation.getParent! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OperationPtr.getRegions!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.pushResult op' ctx newResult hop') =
    operation.getRegions! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushResult {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushResult op' ctx newResult hop') =
    operation.getAttributes! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushResult {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushResult op' ctx newResult hop') =
    opOperand.getNextUse! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushResult {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushResult op' ctx newResult hop') =
    opOperand.getBack! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushResult {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushResult op' ctx newResult hop') =
    opOperand.getOwner! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushResult {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushResult op' ctx newResult hop') =
    opOperand.getValue! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushResult op' ctx newResult hop') =
    blockOperand.getNextUse! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushResult op' ctx newResult hop') =
    blockOperand.getBack! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushResult op' ctx newResult hop') =
    blockOperand.getOwner! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushResult op' ctx newResult hop') =
    blockOperand.getValue! ctx := by
  grind [OperationPtr.getResult]

@[grind =]
theorem OpResultPtr.getType!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushResult op' ctx newResult hop') =
    if opResult = op'.nextResult ctx then
      newResult.type
    else
      opResult.getType! ctx := by
  grind [OperationPtr.getResult]

@[grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushResult op' ctx newResult hop') =
    if opResult = op'.nextResult ctx then
      newResult.firstUse
    else
      opResult.getFirstUse! ctx := by
  grind [OperationPtr.getResult]

@[grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushResult op' ctx newResult hop') =
    if opResult = op'.nextResult ctx then
      newResult.owner
    else
      opResult.getOwner! ctx := by
  grind [OperationPtr.getResult]

@[grind =]
theorem OpResultPtr.getIndex!_OperationPtr_pushResult {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushResult op' ctx newResult hop') =
    if opResult = op'.nextResult ctx then
      newResult.index
    else
      opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushResult {block : BlockPtr} :
    block.getParent! (OperationPtr.pushResult op' ctx newResult hop') =
    block.getParent! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushResult {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushResult op' ctx newResult hop') =
    block.getFirstUse! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushResult {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushResult op' ctx newResult hop') =
    block.getFirstOp! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushResult {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushResult op' ctx newResult hop') =
    block.getLastOp! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushResult {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushResult op' ctx newResult hop') =
    block.getNextBlock! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushResult {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushResult op' ctx newResult hop') =
    block.getPrevBlock! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushResult op' ctx newResult hop') =
    blockArg.getType! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushResult op' ctx newResult hop') =
    blockArg.getFirstUse! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushResult op' ctx newResult hop') =
    blockArg.getIndex! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushResult op' ctx newResult hop') =
    blockArg.getLoc! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushResult op' ctx newResult hop') =
    blockArg.getOwner! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushResult {region : RegionPtr} :
    region.getParent! (OperationPtr.pushResult op' ctx newResult hop') =
    region.getParent! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushResult {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushResult op' ctx newResult hop') =
    region.getFirstBlock! ctx := by
  grind [OperationPtr.getResult]

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushResult {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushResult op' ctx newResult hop') =
    region.getLastBlock! ctx := by
  grind [OperationPtr.getResult]

/- OperationPtr.pushRegion -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getNextOp! (OperationPtr.pushRegion op' ctx newRegion hop') =
    operation.getNextOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getPrevOp!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getPrevOp! (OperationPtr.pushRegion op' ctx newRegion hop') =
    operation.getPrevOp! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getParent!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getParent! (OperationPtr.pushRegion op' ctx newRegion hop') =
    operation.getParent! ctx := by
  grind

@[grind =]
theorem OperationPtr.getRegions!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getRegions! (OperationPtr.pushRegion op' ctx newRegion hop') =
    if operation = op' then
      (operation.getRegions! ctx).push newRegion
    else
      operation.getRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getAttributes!_OperationPtr_pushRegion {operation : OperationPtr} :
    operation.getAttributes! (OperationPtr.pushRegion op' ctx newRegion hop') =
    operation.getAttributes! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getBack!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getBack! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getOwner!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getOwner! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.getValue!_OperationPtr_pushRegion {opOperand : OpOperandPtr} :
    opOperand.getValue! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockOperand.getNextUse! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getBack!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockOperand.getBack! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockOperand.getOwner! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.getValue!_OperationPtr_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockOperand.getValue! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getType!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getType! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opResult.getType! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getFirstUse! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opResult.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getOwner!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getOwner! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opResult.getOwner! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.getIndex!_OperationPtr_pushRegion {opResult : OpResultPtr} :
    opResult.getIndex! (OperationPtr.pushRegion op' ctx newRegion hop') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getParent! (OperationPtr.pushRegion op' ctx newRegion hop') =
    block.getParent! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstUse!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getFirstUse! (OperationPtr.pushRegion op' ctx newRegion hop') =
    block.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getFirstOp!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getFirstOp! (OperationPtr.pushRegion op' ctx newRegion hop') =
    block.getFirstOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getLastOp!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getLastOp! (OperationPtr.pushRegion op' ctx newRegion hop') =
    block.getLastOp! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNextBlock!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getNextBlock! (OperationPtr.pushRegion op' ctx newRegion hop') =
    block.getNextBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_OperationPtr_pushRegion {block : BlockPtr} :
    block.getPrevBlock! (OperationPtr.pushRegion op' ctx newRegion hop') =
    block.getPrevBlock! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getType!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getType! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockArg.getType! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getFirstUse!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockArg.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getIndex!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockArg.getIndex! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getLoc!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockArg.getLoc! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.getOwner!_OperationPtr_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (OperationPtr.pushRegion op' ctx newRegion hop') =
    blockArg.getOwner! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getParent!_OperationPtr_pushRegion {region : RegionPtr} :
    region.getParent! (OperationPtr.pushRegion op' ctx newRegion hop') =
    region.getParent! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_OperationPtr_pushRegion {region : RegionPtr} :
    region.getFirstBlock! (OperationPtr.pushRegion op' ctx newRegion hop') =
    region.getFirstBlock! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.getLastBlock!_OperationPtr_pushRegion {region : RegionPtr} :
    region.getLastBlock! (OperationPtr.pushRegion op' ctx newRegion hop') =
    region.getLastBlock! ctx := by
  grind

/- BlockPtr.allocEmpty -/

@[simp, grind =>]
theorem OperationPtr.getNextOp!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    operation.getNextOp! ctx' =
    operation.getNextOp! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OperationPtr.getPrevOp!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    operation.getPrevOp! ctx' =
    operation.getPrevOp! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OperationPtr.getParent!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    operation.getParent! ctx' =
    operation.getParent! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OperationPtr.getRegions!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    operation.getRegions! ctx' =
    operation.getRegions! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OperationPtr.getAttributes!_BlockPtr_allocEmpty {operation : OperationPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    operation.getAttributes! ctx' =
    operation.getAttributes! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpOperandPtr.getNextUse!_BlockPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpOperandPtr.getBack!_BlockPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpOperandPtr.getOwner!_BlockPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpOperandPtr.getValue!_BlockPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getNextUse!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getBack!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getOwner!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockOperandPtr.getValue!_BlockPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpResultPtr.getType!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpResultPtr.getFirstUse!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpResultPtr.getOwner!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem OpResultPtr.getIndex!_BlockPtr_allocEmpty {opResult : OpResultPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[grind =>]
theorem BlockPtr.getParent!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    block.getParent! ctx' =
    if block = block' then
      none
    else
      block.getParent! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[grind =>]
theorem BlockPtr.getFirstUse!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    block.getFirstUse! ctx' =
    if block = block' then
      none
    else
      block.getFirstUse! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[grind =>]
theorem BlockPtr.getFirstOp!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    block.getFirstOp! ctx' =
    if block = block' then
      none
    else
      block.getFirstOp! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[grind =>]
theorem BlockPtr.getLastOp!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    block.getLastOp! ctx' =
    if block = block' then
      none
    else
      block.getLastOp! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[grind =>]
theorem BlockPtr.getNextBlock!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    block.getNextBlock! ctx' =
    if block = block' then
      none
    else
      block.getNextBlock! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[grind =>]
theorem BlockPtr.getPrevBlock!_BlockPtr_allocEmpty {block : BlockPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    block.getPrevBlock! ctx' =
    if block = block' then
      none
    else
      block.getPrevBlock! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getType!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getIndex!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockArgumentPtr.getOwner!_BlockPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem BlockOperandPtrPtr.get!_BlockPtr_allocEmpty {blockOperandPtr : BlockOperandPtrPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    blockOperandPtr.get! ctx' =
    blockOperandPtr.get! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem RegionPtr.getParent!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    region.getParent! ctx' =
    region.getParent! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem RegionPtr.getFirstBlock!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    region.getFirstBlock! ctx' =
    region.getFirstBlock! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

@[simp, grind =>]
theorem RegionPtr.getLastBlock!_BlockPtr_allocEmpty {region : RegionPtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', block')) :
    region.getLastBlock! ctx' =
    region.getLastBlock! ctx := by
  grind [Block.default_arguments_eq, Block.default_firstUse_eq]

/- BlockPtr.pushArgument -/

@[simp, grind =]
theorem OperationPtr.getNextOp!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getNextOp! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getNextOp! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OperationPtr.getPrevOp!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getPrevOp! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getPrevOp! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OperationPtr.getParent!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getParent! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getParent! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OperationPtr.getRegions!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getRegions! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getRegions! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OperationPtr.getAttributes!_BlockPtr_pushArgument {operation : OperationPtr} :
    operation.getAttributes! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    operation.getAttributes! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpOperandPtr.getNextUse!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getNextUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opOperand.getNextUse! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpOperandPtr.getBack!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getBack! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opOperand.getBack! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpOperandPtr.getOwner!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opOperand.getOwner! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpOperandPtr.getValue!_BlockPtr_pushArgument {opOperand : OpOperandPtr} :
    opOperand.getValue! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opOperand.getValue! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockOperandPtr.getNextUse!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getNextUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getNextUse! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockOperandPtr.getBack!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getBack! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getBack! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockOperandPtr.getOwner!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getOwner! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockOperandPtr.getValue!_BlockPtr_pushArgument {blockOperand : BlockOperandPtr} :
    blockOperand.getValue! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    blockOperand.getValue! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpResultPtr.getType!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getType! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getType! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpResultPtr.getFirstUse!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getFirstUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getFirstUse! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpResultPtr.getOwner!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getOwner! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem OpResultPtr.getIndex!_BlockPtr_pushArgument {opResult : OpResultPtr} :
    opResult.getIndex! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind

@[simp, grind =]
theorem BlockPtr.getParent!_BlockPtr_pushArgument {block : BlockPtr} :
    block.getParent! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    block.getParent! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockPtr.getFirstUse!_BlockPtr_pushArgument {block : BlockPtr} :
    block.getFirstUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    block.getFirstUse! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockPtr.getFirstOp!_BlockPtr_pushArgument {block : BlockPtr} :
    block.getFirstOp! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    block.getFirstOp! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockPtr.getLastOp!_BlockPtr_pushArgument {block : BlockPtr} :
    block.getLastOp! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    block.getLastOp! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockPtr.getNextBlock!_BlockPtr_pushArgument {block : BlockPtr} :
    block.getNextBlock! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    block.getNextBlock! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem BlockPtr.getPrevBlock!_BlockPtr_pushArgument {block : BlockPtr} :
    block.getPrevBlock! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    block.getPrevBlock! ctx := by
  grind [BlockPtr.getArgument]

@[grind =]
theorem BlockArgumentPtr.getType!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getType! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument ctx then
      newArgument.type
    else
      blockArg.getType! ctx := by
  grind [BlockPtr.getArgument]

@[grind =]
theorem BlockArgumentPtr.getFirstUse!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getFirstUse! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument ctx then
      newArgument.firstUse
    else
      blockArg.getFirstUse! ctx := by
  grind [BlockPtr.getArgument]

@[grind =]
theorem BlockArgumentPtr.getIndex!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getIndex! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument ctx then
      newArgument.index
    else
      blockArg.getIndex! ctx := by
  grind [BlockPtr.getArgument]

@[grind =]
theorem BlockArgumentPtr.getLoc!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getLoc! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument ctx then
      newArgument.loc
    else
      blockArg.getLoc! ctx := by
  grind [BlockPtr.getArgument]

@[grind =]
theorem BlockArgumentPtr.getOwner!_BlockPtr_pushArgument {blockArg : BlockArgumentPtr} :
    blockArg.getOwner! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    if blockArg = block'.nextArgument ctx then
      newArgument.owner
    else
      blockArg.getOwner! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem RegionPtr.getParent!_BlockPtr_pushArgument {region : RegionPtr} :
    region.getParent! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.getParent! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem RegionPtr.getFirstBlock!_BlockPtr_pushArgument {region : RegionPtr} :
    region.getFirstBlock! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.getFirstBlock! ctx := by
  grind [BlockPtr.getArgument]

@[simp, grind =]
theorem RegionPtr.getLastBlock!_BlockPtr_pushArgument {region : RegionPtr} :
    region.getLastBlock! (BlockPtr.pushArgument block' ctx newArgument hblock') =
    region.getLastBlock! ctx := by
  grind [BlockPtr.getArgument]

/- RegionPtr.allocEmpty -/

@[simp, grind =>]
theorem OperationPtr.getNextOp!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    operation.getNextOp! ctx' =
    operation.getNextOp! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OperationPtr.getPrevOp!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    operation.getPrevOp! ctx' =
    operation.getPrevOp! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OperationPtr.getParent!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    operation.getParent! ctx' =
    operation.getParent! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OperationPtr.getRegions!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    operation.getRegions! ctx' =
    operation.getRegions! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OperationPtr.getAttributes!_RegionPtr_allocEmpty {operation : OperationPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    operation.getAttributes! ctx' =
    operation.getAttributes! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpOperandPtr.getNextUse!_RegionPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opOperand.getNextUse! ctx' =
    opOperand.getNextUse! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpOperandPtr.getBack!_RegionPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opOperand.getBack! ctx' =
    opOperand.getBack! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpOperandPtr.getOwner!_RegionPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opOperand.getOwner! ctx' =
    opOperand.getOwner! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpOperandPtr.getValue!_RegionPtr_allocEmpty {opOperand : OpOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opOperand.getValue! ctx' =
    opOperand.getValue! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockOperandPtr.getNextUse!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockOperand.getNextUse! ctx' =
    blockOperand.getNextUse! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockOperandPtr.getBack!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockOperand.getBack! ctx' =
    blockOperand.getBack! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockOperandPtr.getOwner!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockOperand.getOwner! ctx' =
    blockOperand.getOwner! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockOperandPtr.getValue!_RegionPtr_allocEmpty {blockOperand : BlockOperandPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockOperand.getValue! ctx' =
    blockOperand.getValue! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpResultPtr.getType!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opResult.getType! ctx' =
    opResult.getType! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpResultPtr.getFirstUse!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opResult.getFirstUse! ctx' =
    opResult.getFirstUse! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpResultPtr.getOwner!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opResult.getOwner! ctx' =
    opResult.getOwner! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem OpResultPtr.getIndex!_RegionPtr_allocEmpty {opResult : OpResultPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    opResult.getIndex! ctx' =
    opResult.getIndex! ctx := by
  simp only [OpResultPtr.getIndex!_def]
  grind [Operation.default_results_eq]

@[simp, grind =>]
theorem BlockPtr.getParent!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    block.getParent! ctx' =
    block.getParent! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockPtr.getFirstUse!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    block.getFirstUse! ctx' =
    block.getFirstUse! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockPtr.getFirstOp!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    block.getFirstOp! ctx' =
    block.getFirstOp! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockPtr.getLastOp!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    block.getLastOp! ctx' =
    block.getLastOp! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockPtr.getNextBlock!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    block.getNextBlock! ctx' =
    block.getNextBlock! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockPtr.getPrevBlock!_RegionPtr_allocEmpty {block : BlockPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    block.getPrevBlock! ctx' =
    block.getPrevBlock! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockArgumentPtr.getType!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockArg.getType! ctx' =
    blockArg.getType! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockArgumentPtr.getFirstUse!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockArg.getFirstUse! ctx' =
    blockArg.getFirstUse! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockArgumentPtr.getIndex!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockArg.getIndex! ctx' =
    blockArg.getIndex! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockArgumentPtr.getOwner!_RegionPtr_allocEmpty {blockArg : BlockArgumentPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    blockArg.getOwner! ctx' =
    blockArg.getOwner! ctx := by
  grind [Region.empty]

@[grind =>]
theorem RegionPtr.getParent!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    region.getParent! ctx' =
    if region = region' then
      none
    else
      region.getParent! ctx := by
  grind [Region.empty]

@[grind =>]
theorem RegionPtr.getFirstBlock!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    region.getFirstBlock! ctx' =
    if region = region' then
      none
    else
      region.getFirstBlock! ctx := by
  grind [Region.empty]

@[grind =>]
theorem RegionPtr.getLastBlock!_RegionPtr_allocEmpty {region : RegionPtr}
    (heq : RegionPtr.allocEmpty ctx = some (ctx', region')) :
    region.getLastBlock! ctx' =
    if region = region' then
      none
    else
      region.getLastBlock! ctx := by
  grind [Region.empty]

@[simp, grind =>]
theorem BlockOperandPtrPtr.get!_OperationPtr_allocEmpty {blockOperandPtr : BlockOperandPtrPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    blockOperandPtr.get! ctx' = blockOperandPtr.get! ctx := by
  grind

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =>]
theorem ValuePtr.getFirstUse!_OperationPtr_allocEmpty {value : ValuePtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind [Operation.default_results_eq, OperationPtr.getOpType!_OperationPtr_allocEmpty, OperationPtr.getNumResults!_OperationPtr_allocEmpty, OperationPtr.getNumOperands!_OperationPtr_allocEmpty, OperationPtr.getProperties!_OperationPtr_allocEmpty, OperationPtr.getOperands!_OperationPtr_allocEmpty, OperationPtr.getNumSuccessors!_OperationPtr_allocEmpty, OperationPtr.getNumRegions!_OperationPtr_allocEmpty, OperationPtr.getRegion!_OperationPtr_allocEmpty, BlockPtr.getNumArguments!_OperationPtr_allocEmpty, OperationPtr.getNextOp!_OperationPtr_allocEmpty, OperationPtr.getPrevOp!_OperationPtr_allocEmpty, OperationPtr.getParent!_OperationPtr_allocEmpty, OperationPtr.getRegions!_OperationPtr_allocEmpty, OperationPtr.getAttributes!_OperationPtr_allocEmpty, OpOperandPtr.getNextUse!_OperationPtr_allocEmpty, OpOperandPtr.getBack!_OperationPtr_allocEmpty, OpOperandPtr.getOwner!_OperationPtr_allocEmpty, OpOperandPtr.getValue!_OperationPtr_allocEmpty, BlockOperandPtr.getNextUse!_OperationPtr_allocEmpty, BlockOperandPtr.getBack!_OperationPtr_allocEmpty, BlockOperandPtr.getOwner!_OperationPtr_allocEmpty, BlockOperandPtr.getValue!_OperationPtr_allocEmpty, OpResultPtr.getType!_OperationPtr_allocEmpty, OpResultPtr.getFirstUse!_OperationPtr_allocEmpty, OpResultPtr.getOwner!_OperationPtr_allocEmpty, BlockPtr.getParent!_OperationPtr_allocEmpty, BlockPtr.getFirstUse!_OperationPtr_allocEmpty, BlockPtr.getFirstOp!_OperationPtr_allocEmpty, BlockPtr.getLastOp!_OperationPtr_allocEmpty, BlockPtr.getNextBlock!_OperationPtr_allocEmpty, BlockPtr.getPrevBlock!_OperationPtr_allocEmpty, BlockArgumentPtr.getType!_OperationPtr_allocEmpty, BlockArgumentPtr.getFirstUse!_OperationPtr_allocEmpty, BlockArgumentPtr.getIndex!_OperationPtr_allocEmpty, BlockArgumentPtr.getOwner!_OperationPtr_allocEmpty, RegionPtr.getParent!_OperationPtr_allocEmpty, RegionPtr.getFirstBlock!_OperationPtr_allocEmpty, RegionPtr.getLastBlock!_OperationPtr_allocEmpty]

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =>]
theorem ValuePtr.getType!_OperationPtr_allocEmpty {value : ValuePtr}
    (h : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    value.getType! ctx' = value.getType! ctx := by
  grind [Operation.default_results_eq, OperationPtr.getOpType!_OperationPtr_allocEmpty, OperationPtr.getNumResults!_OperationPtr_allocEmpty, OperationPtr.getNumOperands!_OperationPtr_allocEmpty, OperationPtr.getProperties!_OperationPtr_allocEmpty, OperationPtr.getOperands!_OperationPtr_allocEmpty, OperationPtr.getNumSuccessors!_OperationPtr_allocEmpty, OperationPtr.getNumRegions!_OperationPtr_allocEmpty, OperationPtr.getRegion!_OperationPtr_allocEmpty, BlockPtr.getNumArguments!_OperationPtr_allocEmpty, OperationPtr.getNextOp!_OperationPtr_allocEmpty, OperationPtr.getPrevOp!_OperationPtr_allocEmpty, OperationPtr.getParent!_OperationPtr_allocEmpty, OperationPtr.getRegions!_OperationPtr_allocEmpty, OperationPtr.getAttributes!_OperationPtr_allocEmpty, OpOperandPtr.getNextUse!_OperationPtr_allocEmpty, OpOperandPtr.getBack!_OperationPtr_allocEmpty, OpOperandPtr.getOwner!_OperationPtr_allocEmpty, OpOperandPtr.getValue!_OperationPtr_allocEmpty, BlockOperandPtr.getNextUse!_OperationPtr_allocEmpty, BlockOperandPtr.getBack!_OperationPtr_allocEmpty, BlockOperandPtr.getOwner!_OperationPtr_allocEmpty, BlockOperandPtr.getValue!_OperationPtr_allocEmpty, OpResultPtr.getType!_OperationPtr_allocEmpty, OpResultPtr.getFirstUse!_OperationPtr_allocEmpty, OpResultPtr.getOwner!_OperationPtr_allocEmpty, BlockPtr.getParent!_OperationPtr_allocEmpty, BlockPtr.getFirstUse!_OperationPtr_allocEmpty, BlockPtr.getFirstOp!_OperationPtr_allocEmpty, BlockPtr.getLastOp!_OperationPtr_allocEmpty, BlockPtr.getNextBlock!_OperationPtr_allocEmpty, BlockPtr.getPrevBlock!_OperationPtr_allocEmpty, BlockArgumentPtr.getType!_OperationPtr_allocEmpty, BlockArgumentPtr.getFirstUse!_OperationPtr_allocEmpty, BlockArgumentPtr.getIndex!_OperationPtr_allocEmpty, BlockArgumentPtr.getOwner!_OperationPtr_allocEmpty, RegionPtr.getParent!_OperationPtr_allocEmpty, RegionPtr.getFirstBlock!_OperationPtr_allocEmpty, RegionPtr.getLastBlock!_OperationPtr_allocEmpty, ValuePtr.getFirstUse!_OperationPtr_allocEmpty]

@[simp, grind =>]
theorem OpOperandPtrPtr.get!_OperationPtr_allocEmpty {opOperandPtr : OpOperandPtrPtr}
    (heq : OperationPtr.allocEmpty ctx ty properties = some (ctx', op')) :
    opOperandPtr.get! ctx' = opOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumResults! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumResults! ctx := by
  grind [OperationPtr.InBounds]

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumOperands! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumOperands! ctx := by
  grind [OperationPtr.InBounds]

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =]
theorem OperationPtr.getOperands!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getOperands! (OperationPtr.dealloc operation' ctx hop') =
    operation.getOperands! ctx := by
  grind [OperationPtr.getOpType!_OperationPtr_dealloc, OperationPtr.getProperties!_OperationPtr_dealloc, BlockPtr.getNumArguments!_OperationPtr_dealloc, OperationPtr.getNextOp!_OperationPtr_dealloc, OperationPtr.getPrevOp!_OperationPtr_dealloc, OperationPtr.getParent!_OperationPtr_dealloc, OperationPtr.getRegions!_OperationPtr_dealloc, OperationPtr.getAttributes!_OperationPtr_dealloc, OpOperandPtr.getNextUse!_OperationPtr_dealloc, OpOperandPtr.getBack!_OperationPtr_dealloc, OpOperandPtr.getOwner!_OperationPtr_dealloc, OpOperandPtr.getValue!_OperationPtr_dealloc, BlockOperandPtr.getNextUse!_OperationPtr_dealloc, BlockOperandPtr.getBack!_OperationPtr_dealloc, BlockOperandPtr.getOwner!_OperationPtr_dealloc, BlockOperandPtr.getValue!_OperationPtr_dealloc, OpResultPtr.getType!_OperationPtr_dealloc, OpResultPtr.getFirstUse!_OperationPtr_dealloc, OpResultPtr.getOwner!_OperationPtr_dealloc, BlockPtr.getParent!_OperationPtr_dealloc, BlockPtr.getFirstUse!_OperationPtr_dealloc, BlockPtr.getFirstOp!_OperationPtr_dealloc, BlockPtr.getLastOp!_OperationPtr_dealloc, BlockPtr.getNextBlock!_OperationPtr_dealloc, BlockPtr.getPrevBlock!_OperationPtr_dealloc, BlockArgumentPtr.getType!_OperationPtr_dealloc, BlockArgumentPtr.getFirstUse!_OperationPtr_dealloc, BlockArgumentPtr.getIndex!_OperationPtr_dealloc, BlockArgumentPtr.getLoc!_OperationPtr_dealloc, BlockArgumentPtr.getOwner!_OperationPtr_dealloc, RegionPtr.getParent!_OperationPtr_dealloc, RegionPtr.getFirstBlock!_OperationPtr_dealloc, RegionPtr.getLastBlock!_OperationPtr_dealloc, OperationPtr.getNumResults!_OperationPtr_dealloc, OperationPtr.getNumOperands!_OperationPtr_dealloc]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OperationPtr_dealloc {operation : OperationPtr} :
    operation.InBounds (OperationPtr.dealloc operation' ctx hop') →
    operation.getNumSuccessors! (OperationPtr.dealloc operation' ctx hop') =
    operation.getNumSuccessors! ctx := by
  grind [OperationPtr.InBounds]

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

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_dealloc {value : ValuePtr} :
    value.InBounds (OperationPtr.dealloc operation' ctx hop') →
    value.getFirstUse! (OperationPtr.dealloc operation' ctx hop') =
    value.getFirstUse! ctx := by
  grind [OpResultPtr.InBounds, OperationPtr.getOpType!_OperationPtr_dealloc, OperationPtr.getProperties!_OperationPtr_dealloc, BlockPtr.getNumArguments!_OperationPtr_dealloc, OperationPtr.getNextOp!_OperationPtr_dealloc, OperationPtr.getPrevOp!_OperationPtr_dealloc, OperationPtr.getParent!_OperationPtr_dealloc, OperationPtr.getRegions!_OperationPtr_dealloc, OperationPtr.getAttributes!_OperationPtr_dealloc, OpOperandPtr.getNextUse!_OperationPtr_dealloc, OpOperandPtr.getBack!_OperationPtr_dealloc, OpOperandPtr.getOwner!_OperationPtr_dealloc, OpOperandPtr.getValue!_OperationPtr_dealloc, BlockOperandPtr.getNextUse!_OperationPtr_dealloc, BlockOperandPtr.getBack!_OperationPtr_dealloc, BlockOperandPtr.getOwner!_OperationPtr_dealloc, BlockOperandPtr.getValue!_OperationPtr_dealloc, OpResultPtr.getType!_OperationPtr_dealloc, OpResultPtr.getFirstUse!_OperationPtr_dealloc, OpResultPtr.getOwner!_OperationPtr_dealloc, BlockPtr.getParent!_OperationPtr_dealloc, BlockPtr.getFirstUse!_OperationPtr_dealloc, BlockPtr.getFirstOp!_OperationPtr_dealloc, BlockPtr.getLastOp!_OperationPtr_dealloc, BlockPtr.getNextBlock!_OperationPtr_dealloc, BlockPtr.getPrevBlock!_OperationPtr_dealloc, BlockArgumentPtr.getType!_OperationPtr_dealloc, BlockArgumentPtr.getFirstUse!_OperationPtr_dealloc, BlockArgumentPtr.getIndex!_OperationPtr_dealloc, BlockArgumentPtr.getLoc!_OperationPtr_dealloc, BlockArgumentPtr.getOwner!_OperationPtr_dealloc, RegionPtr.getParent!_OperationPtr_dealloc, RegionPtr.getFirstBlock!_OperationPtr_dealloc, RegionPtr.getLastBlock!_OperationPtr_dealloc, OperationPtr.getNumResults!_OperationPtr_dealloc, OperationPtr.getNumOperands!_OperationPtr_dealloc, OperationPtr.getOperands!_OperationPtr_dealloc, OperationPtr.getNumSuccessors!_OperationPtr_dealloc, OperationPtr.getNumRegions!_OperationPtr_dealloc, OperationPtr.getRegion!_OperationPtr_dealloc]

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =]
theorem ValuePtr.getType!_OperationPtr_dealloc {value : ValuePtr} :
    value.InBounds (OperationPtr.dealloc operation' ctx hop') →
    value.getType! (OperationPtr.dealloc operation' ctx hop') =
    value.getType! ctx := by
  grind [OpResultPtr.InBounds, OperationPtr.getOpType!_OperationPtr_dealloc, OperationPtr.getProperties!_OperationPtr_dealloc, BlockPtr.getNumArguments!_OperationPtr_dealloc, OperationPtr.getNextOp!_OperationPtr_dealloc, OperationPtr.getPrevOp!_OperationPtr_dealloc, OperationPtr.getParent!_OperationPtr_dealloc, OperationPtr.getRegions!_OperationPtr_dealloc, OperationPtr.getAttributes!_OperationPtr_dealloc, OpOperandPtr.getNextUse!_OperationPtr_dealloc, OpOperandPtr.getBack!_OperationPtr_dealloc, OpOperandPtr.getOwner!_OperationPtr_dealloc, OpOperandPtr.getValue!_OperationPtr_dealloc, BlockOperandPtr.getNextUse!_OperationPtr_dealloc, BlockOperandPtr.getBack!_OperationPtr_dealloc, BlockOperandPtr.getOwner!_OperationPtr_dealloc, BlockOperandPtr.getValue!_OperationPtr_dealloc, OpResultPtr.getType!_OperationPtr_dealloc, OpResultPtr.getFirstUse!_OperationPtr_dealloc, OpResultPtr.getOwner!_OperationPtr_dealloc, BlockPtr.getParent!_OperationPtr_dealloc, BlockPtr.getFirstUse!_OperationPtr_dealloc, BlockPtr.getFirstOp!_OperationPtr_dealloc, BlockPtr.getLastOp!_OperationPtr_dealloc, BlockPtr.getNextBlock!_OperationPtr_dealloc, BlockPtr.getPrevBlock!_OperationPtr_dealloc, BlockArgumentPtr.getType!_OperationPtr_dealloc, BlockArgumentPtr.getFirstUse!_OperationPtr_dealloc, BlockArgumentPtr.getIndex!_OperationPtr_dealloc, BlockArgumentPtr.getLoc!_OperationPtr_dealloc, BlockArgumentPtr.getOwner!_OperationPtr_dealloc, RegionPtr.getParent!_OperationPtr_dealloc, RegionPtr.getFirstBlock!_OperationPtr_dealloc, RegionPtr.getLastBlock!_OperationPtr_dealloc, OperationPtr.getNumResults!_OperationPtr_dealloc, OperationPtr.getNumOperands!_OperationPtr_dealloc, OperationPtr.getOperands!_OperationPtr_dealloc, OperationPtr.getNumSuccessors!_OperationPtr_dealloc, OperationPtr.getNumRegions!_OperationPtr_dealloc, OperationPtr.getRegion!_OperationPtr_dealloc, ValuePtr.getFirstUse!_OperationPtr_dealloc]

@[simp, grind =]
theorem OpOperandPtrPtr.get!_OperationPtr_dealloc {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.InBounds (OperationPtr.dealloc operation' ctx hop') →
    opOperandPtr.get! (OperationPtr.dealloc operation' ctx hop') =
    opOperandPtr.get! ctx := by
  grind [OpOperandPtr.InBounds]

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
        opOperand.getNextUse! ctx := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_OperationPtr_pushBlockOperand {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (OperationPtr.pushBlockOperand operation' ctx newOperand hop') =
    if blockOperandPtr = .blockOperandNextUse (operation'.nextBlockOperand ctx) then
      newOperand.nextUse
    else
      blockOperandPtr.get! ctx := by
  grind

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[grind =]
theorem ValuePtr.getFirstUse!_OperationPtr_pushResult {value : ValuePtr} :
    value.getFirstUse! (OperationPtr.pushResult operation' ctx newResult hop') =
    if value = ValuePtr.opResult (operation'.nextResult ctx) then
      newResult.firstUse
    else
      value.getFirstUse! ctx := by
  grind [OperationPtr.getProperties!_OperationPtr_pushResult, OperationPtr.getOpType!_OperationPtr_pushResult, OperationPtr.getNumResults!_OperationPtr_pushResult, OperationPtr.getNumOperands!_OperationPtr_pushResult, OperationPtr.getOperands!_OperationPtr_pushResult, OperationPtr.getNumSuccessors!_OperationPtr_pushResult, OperationPtr.getNumRegions!_OperationPtr_pushResult, OperationPtr.getRegion!_OperationPtr_pushResult, BlockPtr.getNumArguments!_OperationPtr_pushResult, OperationPtr.getNextOp!_OperationPtr_pushResult, OperationPtr.getPrevOp!_OperationPtr_pushResult, OperationPtr.getParent!_OperationPtr_pushResult, OperationPtr.getRegions!_OperationPtr_pushResult, OperationPtr.getAttributes!_OperationPtr_pushResult, OpOperandPtr.getNextUse!_OperationPtr_pushResult, OpOperandPtr.getBack!_OperationPtr_pushResult, OpOperandPtr.getOwner!_OperationPtr_pushResult, OpOperandPtr.getValue!_OperationPtr_pushResult, BlockOperandPtr.getNextUse!_OperationPtr_pushResult, BlockOperandPtr.getBack!_OperationPtr_pushResult, BlockOperandPtr.getOwner!_OperationPtr_pushResult, BlockOperandPtr.getValue!_OperationPtr_pushResult, OpResultPtr.getType!_OperationPtr_pushResult, OpResultPtr.getFirstUse!_OperationPtr_pushResult, OpResultPtr.getOwner!_OperationPtr_pushResult, BlockPtr.getParent!_OperationPtr_pushResult, BlockPtr.getFirstUse!_OperationPtr_pushResult, BlockPtr.getFirstOp!_OperationPtr_pushResult, BlockPtr.getLastOp!_OperationPtr_pushResult, BlockPtr.getNextBlock!_OperationPtr_pushResult, BlockPtr.getPrevBlock!_OperationPtr_pushResult, BlockArgumentPtr.getType!_OperationPtr_pushResult, BlockArgumentPtr.getFirstUse!_OperationPtr_pushResult, BlockArgumentPtr.getIndex!_OperationPtr_pushResult, BlockArgumentPtr.getLoc!_OperationPtr_pushResult, BlockArgumentPtr.getOwner!_OperationPtr_pushResult, RegionPtr.getParent!_OperationPtr_pushResult, RegionPtr.getFirstBlock!_OperationPtr_pushResult, RegionPtr.getLastBlock!_OperationPtr_pushResult]

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[grind =]
theorem ValuePtr.getType!_OperationPtr_pushResult {value : ValuePtr} :
    value.getType! (OperationPtr.pushResult operation' ctx newResult hop') =
    if value = ValuePtr.opResult (operation'.nextResult ctx) then
      newResult.type
    else
      value.getType! ctx := by
  grind [OperationPtr.getProperties!_OperationPtr_pushResult, OperationPtr.getOpType!_OperationPtr_pushResult, OperationPtr.getNumResults!_OperationPtr_pushResult, OperationPtr.getNumOperands!_OperationPtr_pushResult, OperationPtr.getOperands!_OperationPtr_pushResult, OperationPtr.getNumSuccessors!_OperationPtr_pushResult, OperationPtr.getNumRegions!_OperationPtr_pushResult, OperationPtr.getRegion!_OperationPtr_pushResult, BlockPtr.getNumArguments!_OperationPtr_pushResult, OperationPtr.getNextOp!_OperationPtr_pushResult, OperationPtr.getPrevOp!_OperationPtr_pushResult, OperationPtr.getParent!_OperationPtr_pushResult, OperationPtr.getRegions!_OperationPtr_pushResult, OperationPtr.getAttributes!_OperationPtr_pushResult, OpOperandPtr.getNextUse!_OperationPtr_pushResult, OpOperandPtr.getBack!_OperationPtr_pushResult, OpOperandPtr.getOwner!_OperationPtr_pushResult, OpOperandPtr.getValue!_OperationPtr_pushResult, BlockOperandPtr.getNextUse!_OperationPtr_pushResult, BlockOperandPtr.getBack!_OperationPtr_pushResult, BlockOperandPtr.getOwner!_OperationPtr_pushResult, BlockOperandPtr.getValue!_OperationPtr_pushResult, OpResultPtr.getType!_OperationPtr_pushResult, OpResultPtr.getFirstUse!_OperationPtr_pushResult, OpResultPtr.getOwner!_OperationPtr_pushResult, BlockPtr.getParent!_OperationPtr_pushResult, BlockPtr.getFirstUse!_OperationPtr_pushResult, BlockPtr.getFirstOp!_OperationPtr_pushResult, BlockPtr.getLastOp!_OperationPtr_pushResult, BlockPtr.getNextBlock!_OperationPtr_pushResult, BlockPtr.getPrevBlock!_OperationPtr_pushResult, BlockArgumentPtr.getType!_OperationPtr_pushResult, BlockArgumentPtr.getFirstUse!_OperationPtr_pushResult, BlockArgumentPtr.getIndex!_OperationPtr_pushResult, BlockArgumentPtr.getLoc!_OperationPtr_pushResult, BlockArgumentPtr.getOwner!_OperationPtr_pushResult, RegionPtr.getParent!_OperationPtr_pushResult, RegionPtr.getFirstBlock!_OperationPtr_pushResult, RegionPtr.getLastBlock!_OperationPtr_pushResult, ValuePtr.getFirstUse!_OperationPtr_pushResult]

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =>]
theorem ValuePtr.getFirstUse!_BlockPtr_allocEmpty {value : ValuePtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    value.getFirstUse! ctx' = value.getFirstUse! ctx := by
  grind [OperationPtr.getOpType!_BlockPtr_allocEmpty, OperationPtr.getProperties!_BlockPtr_allocEmpty, OperationPtr.getNumResults!_BlockPtr_allocEmpty, OperationPtr.getNumOperands!_BlockPtr_allocEmpty, OperationPtr.getOperands!_BlockPtr_allocEmpty, OperationPtr.getNumSuccessors!_BlockPtr_allocEmpty, OperationPtr.getNumRegions!_BlockPtr_allocEmpty, OperationPtr.getRegion!_BlockPtr_allocEmpty, BlockPtr.getNumArguments!_BlockPtr_allocEmpty, OperationPtr.getNextOp!_BlockPtr_allocEmpty, OperationPtr.getPrevOp!_BlockPtr_allocEmpty, OperationPtr.getParent!_BlockPtr_allocEmpty, OperationPtr.getRegions!_BlockPtr_allocEmpty, OperationPtr.getAttributes!_BlockPtr_allocEmpty, OpOperandPtr.getNextUse!_BlockPtr_allocEmpty, OpOperandPtr.getBack!_BlockPtr_allocEmpty, OpOperandPtr.getOwner!_BlockPtr_allocEmpty, OpOperandPtr.getValue!_BlockPtr_allocEmpty, BlockOperandPtr.getNextUse!_BlockPtr_allocEmpty, BlockOperandPtr.getBack!_BlockPtr_allocEmpty, BlockOperandPtr.getOwner!_BlockPtr_allocEmpty, BlockOperandPtr.getValue!_BlockPtr_allocEmpty, OpResultPtr.getType!_BlockPtr_allocEmpty, OpResultPtr.getFirstUse!_BlockPtr_allocEmpty, OpResultPtr.getOwner!_BlockPtr_allocEmpty, BlockPtr.getParent!_BlockPtr_allocEmpty, BlockPtr.getFirstUse!_BlockPtr_allocEmpty, BlockPtr.getFirstOp!_BlockPtr_allocEmpty, BlockPtr.getLastOp!_BlockPtr_allocEmpty, BlockPtr.getNextBlock!_BlockPtr_allocEmpty, BlockPtr.getPrevBlock!_BlockPtr_allocEmpty, BlockArgumentPtr.getType!_BlockPtr_allocEmpty, BlockArgumentPtr.getFirstUse!_BlockPtr_allocEmpty, BlockArgumentPtr.getIndex!_BlockPtr_allocEmpty, BlockArgumentPtr.getOwner!_BlockPtr_allocEmpty, RegionPtr.getParent!_BlockPtr_allocEmpty, RegionPtr.getFirstBlock!_BlockPtr_allocEmpty, RegionPtr.getLastBlock!_BlockPtr_allocEmpty]

attribute [local grind _=_] BlockArgumentPtr.getFirstUse!_def BlockArgumentPtr.getFirstUse_def BlockArgumentPtr.getIndex!_def BlockArgumentPtr.getIndex_def BlockArgumentPtr.getLoc!_def BlockArgumentPtr.getLoc_def BlockArgumentPtr.getOwner!_def BlockArgumentPtr.getOwner_def BlockArgumentPtr.getType!_def BlockArgumentPtr.getType_def BlockOperandPtr.getBack!_def BlockOperandPtr.getBack_def BlockOperandPtr.getNextUse!_def BlockOperandPtr.getNextUse_def BlockOperandPtr.getOwner!_def BlockOperandPtr.getOwner_def BlockOperandPtr.getValue!_def BlockOperandPtr.getValue_def BlockPtr.getFirstOp!_def BlockPtr.getFirstOp_def BlockPtr.getFirstUse!_def BlockPtr.getFirstUse_def BlockPtr.getLastOp!_def BlockPtr.getLastOp_def BlockPtr.getNextBlock!_def BlockPtr.getNextBlock_def BlockPtr.getParent!_def BlockPtr.getParent_def BlockPtr.getPrevBlock!_def BlockPtr.getPrevBlock_def OpOperandPtr.getBack!_def OpOperandPtr.getBack_def OpOperandPtr.getNextUse!_def OpOperandPtr.getNextUse_def OpOperandPtr.getOwner!_def OpOperandPtr.getOwner_def OpOperandPtr.getValue!_def OpOperandPtr.getValue_def OpResultPtr.getFirstUse!_def OpResultPtr.getFirstUse_def OpResultPtr.getOwner!_def OpResultPtr.getOwner_def OpResultPtr.getType!_def OpResultPtr.getType_def OperationPtr.getAttributes!_def OperationPtr.getAttributes_def OperationPtr.getNextOp!_def OperationPtr.getNextOp_def OperationPtr.getOpType!_def OperationPtr.getParent!_def OperationPtr.getParent_def OperationPtr.getPrevOp!_def OperationPtr.getPrevOp_def OperationPtr.getRegions!_def RegionPtr.getFirstBlock!_def RegionPtr.getFirstBlock_def RegionPtr.getLastBlock!_def RegionPtr.getLastBlock_def RegionPtr.getParent!_def RegionPtr.getParent_def in
@[simp, grind =>]
theorem ValuePtr.getType!_BlockPtr_allocEmpty {value : ValuePtr}
    (heq : BlockPtr.allocEmpty ctx = some (ctx', bl')) :
    value.getType! ctx' = value.getType! ctx := by
  grind [OperationPtr.getOpType!_BlockPtr_allocEmpty, OperationPtr.getProperties!_BlockPtr_allocEmpty, OperationPtr.getNumResults!_BlockPtr_allocEmpty, OperationPtr.getNumOperands!_BlockPtr_allocEmpty, OperationPtr.getOperands!_BlockPtr_allocEmpty, OperationPtr.getNumSuccessors!_BlockPtr_allocEmpty, OperationPtr.getNumRegions!_BlockPtr_allocEmpty, OperationPtr.getRegion!_BlockPtr_allocEmpty, BlockPtr.getNumArguments!_BlockPtr_allocEmpty, OperationPtr.getNextOp!_BlockPtr_allocEmpty, OperationPtr.getPrevOp!_BlockPtr_allocEmpty, OperationPtr.getParent!_BlockPtr_allocEmpty, OperationPtr.getRegions!_BlockPtr_allocEmpty, OperationPtr.getAttributes!_BlockPtr_allocEmpty, OpOperandPtr.getNextUse!_BlockPtr_allocEmpty, OpOperandPtr.getBack!_BlockPtr_allocEmpty, OpOperandPtr.getOwner!_BlockPtr_allocEmpty, OpOperandPtr.getValue!_BlockPtr_allocEmpty, BlockOperandPtr.getNextUse!_BlockPtr_allocEmpty, BlockOperandPtr.getBack!_BlockPtr_allocEmpty, BlockOperandPtr.getOwner!_BlockPtr_allocEmpty, BlockOperandPtr.getValue!_BlockPtr_allocEmpty, OpResultPtr.getType!_BlockPtr_allocEmpty, OpResultPtr.getFirstUse!_BlockPtr_allocEmpty, OpResultPtr.getOwner!_BlockPtr_allocEmpty, BlockPtr.getParent!_BlockPtr_allocEmpty, BlockPtr.getFirstUse!_BlockPtr_allocEmpty, BlockPtr.getFirstOp!_BlockPtr_allocEmpty, BlockPtr.getLastOp!_BlockPtr_allocEmpty, BlockPtr.getNextBlock!_BlockPtr_allocEmpty, BlockPtr.getPrevBlock!_BlockPtr_allocEmpty, BlockArgumentPtr.getType!_BlockPtr_allocEmpty, BlockArgumentPtr.getFirstUse!_BlockPtr_allocEmpty, BlockArgumentPtr.getIndex!_BlockPtr_allocEmpty, BlockArgumentPtr.getOwner!_BlockPtr_allocEmpty, RegionPtr.getParent!_BlockPtr_allocEmpty, RegionPtr.getFirstBlock!_BlockPtr_allocEmpty, RegionPtr.getLastBlock!_BlockPtr_allocEmpty, ValuePtr.getFirstUse!_BlockPtr_allocEmpty]

end

end Veir
