module

public import Veir.Rewriter.Basic

/-!
Getter lemmas for the specification-level construction steps used by `createOp`.

`pushOperand` and `pushBlockOperand` append an unattached use. The `Sim`
`pushOperandAt` and `pushBlockOperandAt` wrappers attach it afterwards with
`insertIntoCurrent`; appending alone does not update the target's use chain.
Capacities are preserved by all four pushes, while the corresponding length grows.
-/

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}


section Rewriter.pushResult

variable {op : OperationPtr}

attribute [local grind] Rewriter.pushResult

@[simp, grind =]
theorem BlockPtr.get!_pushResult {block : BlockPtr} :
    block.get! (Rewriter.pushResult ctx op type hop) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_pushResult {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushResult ctx op type hop) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushResult {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushResult ctx op type hop) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[grind =]
theorem OperationPtr.getNumResults!_pushResult {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushResult ctx op type hop) =
    if operation = op then operation.getNumResults! ctx + 1
    else operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_pushResult {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushResult ctx op type hop) =
    if opResult = op.nextResult ctx then
      { type := type, firstUse := none, index := op.getNumResults! ctx, owner := op }
    else opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushResult {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushResult ctx op type hop) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_pushResult {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushResult ctx op type hop) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushResult {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushResult ctx op type hop) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_pushResult {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushResult ctx op type hop) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_pushResult {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushResult ctx op type hop) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_pushResult {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushResult ctx op type hop) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_pushResult {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushResult ctx op type hop) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[simp, grind =]
theorem OperationPtr.getNumRegions!_pushResult {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushResult ctx op type hop) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_pushResult {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushResult ctx op type hop) idx =
    operation.getRegion! ctx idx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_pushResult {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushResult ctx op type hop) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushResult {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushResult ctx op type hop) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushResult {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushResult ctx op type hop) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_pushResult {region : RegionPtr} :
    region.get! (Rewriter.pushResult ctx op type hop) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_pushResult {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushResult ctx op type hop) =
    if value = op.nextResult ctx then
      none
    else
      value.getFirstUse! ctx := by
  grind

@[grind =]
theorem ValuePtr.getType!_pushResult {value : ValuePtr} :
    value.getType! (Rewriter.pushResult ctx op type hop) =
    if value = op.nextResult ctx then
      type
    else
      value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_pushResult {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushResult ctx op type hop) =
    if opOperandPtr = OpOperandPtrPtr.valueFirstUse (op.nextResult ctx) then
      none
    else
      opOperandPtr.get! ctx := by
  grind


@[simp, grind =]
theorem OperationPtr.capResults!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).capResults = (operation.get! ctx).capResults := by
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).capRegions = (operation.get! ctx).capRegions := by
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).capOperands = (operation.get! ctx).capOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_pushResult {operation : OperationPtr} :
    (operation.get! (Rewriter.pushResult ctx op type hop)).capBlockOperands = (operation.get! ctx).capBlockOperands := by
  grind

@[grind =]
theorem Rewriter.pushResult_spec_inBounds (ptr : GenericPtr) :
    ptr.InBounds (Rewriter.pushResult ctx op type hop) ↔
    (ptr.InBounds ctx ∨
      ptr = .opResult (op.nextResult ctx) ∨
      ptr = .value (op.nextResult ctx) ∨
      ptr = .opOperandPtr (.valueFirstUse (op.nextResult ctx))) := by
  grind

@[grind =]
theorem Rewriter.pushResult_spec_topLevel_inBounds (ptr : TopLevelPtr) :
    ptr.InBounds (Rewriter.pushResult ctx op type hop) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.pushResult_spec_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (Rewriter.pushResult ctx op type hop).FieldsInBounds := by
  grind [OpResult.FieldsInBounds]

end Rewriter.pushResult

section Rewriter.pushRegion

variable {op : OperationPtr}

attribute [local grind] Rewriter.pushRegion

@[simp, grind =]
theorem BlockPtr.get!_pushRegion {block : BlockPtr} :
    block.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_pushRegion {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushRegion {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushRegion ctx op region hop hregion hregionParent) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_pushRegion {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_pushRegion {opResult : OpResultPtr} :
    opResult.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushRegion {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_pushRegion {opOperand : OpOperandPtr} :
    opOperand.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushRegion {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_pushRegion {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_pushRegion {blockOperand : BlockOperandPtr} :
    blockOperand.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getSuccessor!_pushRegion {operation : OperationPtr} :
    operation.getSuccessor! (Rewriter.pushRegion ctx op region hop hregion hregionParent) index =
    operation.getSuccessor! ctx index := by
  grind [OperationPtr.getSuccessor!_def]

@[simp, grind =]
theorem OperationPtr.getSuccessors!_pushRegion {operation : OperationPtr} :
    operation.getSuccessors! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    operation.getSuccessors! ctx := by
  grind [OperationPtr.getSuccessors!_def]

@[grind =]
theorem OperationPtr.getNumRegions!_pushRegion {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    if operation = op then operation.getNumRegions! ctx + 1
    else operation.getNumRegions! ctx := by
  grind

@[grind =]
theorem OperationPtr.getRegion!_pushRegion {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushRegion ctx op region hop hregion hregionParent) index =
    if operation = op ∧ index = operation.getNumRegions! ctx then region
    else operation.getRegion! ctx index := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_pushRegion {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushRegion {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushRegion {blockArg : BlockArgumentPtr} :
    blockArg.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.firstBlock!_pushRegion {r : RegionPtr} :
    (r.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).firstBlock =
    (r.get! ctx).firstBlock := by
  grind

@[simp, grind =]
theorem RegionPtr.lastBlock!_pushRegion {r : RegionPtr} :
    (r.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).lastBlock =
    (r.get! ctx).lastBlock := by
  grind

@[grind =]
theorem RegionPtr.parent!_pushRegion {r : RegionPtr} :
    (r.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).parent =
    if r = region then some op else (r.get! ctx).parent := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_pushRegion {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_pushRegion {value : ValuePtr} :
    value.getType! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    value.getType! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_pushRegion {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent) =
    opOperandPtr.get! ctx := by
  grind


@[simp, grind =]
theorem OperationPtr.capResults!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).capResults = (operation.get! ctx).capResults := by
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).capRegions = (operation.get! ctx).capRegions := by
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).capOperands = (operation.get! ctx).capOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_pushRegion {operation : OperationPtr} :
    (operation.get! (Rewriter.pushRegion ctx op region hop hregion hregionParent)).capBlockOperands = (operation.get! ctx).capBlockOperands := by
  grind

@[grind =]
theorem Rewriter.pushRegion_spec_inBounds (ptr : GenericPtr) :
    ptr.InBounds (Rewriter.pushRegion ctx op region hop hregion hregionParent) ↔
    (ptr.InBounds ctx) := by
  grind

@[grind =]
theorem Rewriter.pushRegion_spec_topLevel_inBounds (ptr : TopLevelPtr) :
    ptr.InBounds (Rewriter.pushRegion ctx op region hop hregion hregionParent) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.pushRegion_spec_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (Rewriter.pushRegion ctx op region hop hregion hregionParent).FieldsInBounds := by
  grind

end Rewriter.pushRegion

section Rewriter.pushOperand

variable {op : OperationPtr} {target : ValuePtr}

attribute [local grind] Rewriter.pushOperand

@[simp, grind =]
theorem OperationPtr.prev!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.capResults!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).capResults =
    (operation.get! ctx).capResults := by
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).capRegions =
    (operation.get! ctx).capRegions := by
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).capOperands =
    (operation.get! ctx).capOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_pushOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushOperand ctx op target hop htarget)).capBlockOperands =
    (operation.get! ctx).capBlockOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_pushOperand {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushOperand ctx op target hop htarget) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_pushOperand {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushOperand ctx op target hop htarget) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumOperands!_pushOperand {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushOperand ctx op target hop htarget) =
    if operation = op then operation.getNumOperands! ctx + 1 else operation.getNumOperands! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_pushOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushOperand ctx op target hop htarget) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_pushOperand {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushOperand ctx op target hop htarget) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushOperand {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushOperand ctx op target hop htarget) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_pushOperand {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushOperand ctx op target hop htarget) index =
    operation.getRegion! ctx index := by
  grind

@[simp, grind =]
theorem BlockPtr.get!_pushOperand {ptr : BlockPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_pushOperand {ptr : RegionPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushOperand {ptr : BlockArgumentPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_pushOperand {ptr : OpResultPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_pushOperand {ptr : BlockOperandPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushOperand {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushOperand ctx op target hop htarget) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_pushOperand {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushOperand ctx op target hop htarget) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_pushOperand {value : ValuePtr} :
    value.getType! (Rewriter.pushOperand ctx op target hop htarget) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_pushOperand {operand : OpOperandPtr} :
    operand.get! (Rewriter.pushOperand ctx op target hop htarget) =
    if operand = op.nextOperand ctx then
      { value := target, owner := op, back := .valueFirstUse target, nextUse := none }
    else operand.get! ctx := by
  grind

@[grind =]
theorem OperationPtr.getOperands!_pushOperand {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushOperand ctx op target hop htarget) =
    if operation = op then (operation.getOperands! ctx).push target
    else operation.getOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_pushOperand {ptr : OpOperandPtrPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    if ptr = .operandNextUse (op.nextOperand ctx) then none else ptr.get! ctx := by
  cases ptr <;> grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_pushOperand {ptr : BlockOperandPtrPtr} :
    ptr.get! (Rewriter.pushOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[grind =]
theorem Rewriter.pushOperand_spec_inBounds (ptr : GenericPtr) :
    ptr.InBounds (Rewriter.pushOperand ctx op target hop htarget) ↔
    (ptr.InBounds ctx ∨
      ptr = .opOperand (op.nextOperand ctx) ∨
      ptr = .opOperandPtr (.operandNextUse (op.nextOperand ctx))) := by
  grind

@[grind =]
theorem Rewriter.pushOperand_spec_topLevel_inBounds (ptr : TopLevelPtr) :
    ptr.InBounds (Rewriter.pushOperand ctx op target hop htarget) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.pushOperand_spec_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (Rewriter.pushOperand ctx op target hop htarget).FieldsInBounds := by
  grind [OpOperand.FieldsInBounds]

end Rewriter.pushOperand

section Rewriter.pushBlockOperand

variable {op : OperationPtr} {target : BlockPtr}

attribute [local grind] Rewriter.pushBlockOperand

@[simp, grind =]
theorem OperationPtr.prev!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.capResults!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).capResults =
    (operation.get! ctx).capResults := by
  grind

@[simp, grind =]
theorem OperationPtr.capRegions!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).capRegions =
    (operation.get! ctx).capRegions := by
  grind

@[simp, grind =]
theorem OperationPtr.capOperands!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).capOperands =
    (operation.get! ctx).capOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.capBlockOperands!_pushBlockOperand {operation : OperationPtr} :
    (operation.get! (Rewriter.pushBlockOperand ctx op target hop htarget)).capBlockOperands =
    (operation.get! ctx).capBlockOperands := by
  grind

@[simp, grind =]
theorem OperationPtr.getOpType!_pushBlockOperand {operation : OperationPtr} :
    operation.getOpType! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    operation.getOpType! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumResults! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    operation.getNumResults! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumOperands! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OperationPtr.getNumSuccessors!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumSuccessors! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    if operation = op then operation.getNumSuccessors! ctx + 1 else operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_pushBlockOperand {operation : OperationPtr} :
    operation.getNumRegions! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getProperties!_pushBlockOperand {operation : OperationPtr} :
    operation.getProperties! (Rewriter.pushBlockOperand ctx op target hop htarget) opCode =
    operation.getProperties! ctx opCode := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_pushBlockOperand {operation : OperationPtr} :
    operation.getRegion! (Rewriter.pushBlockOperand ctx op target hop htarget) index =
    operation.getRegion! ctx index := by
  grind

@[simp, grind =]
theorem BlockPtr.get!_pushBlockOperand {ptr : BlockPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_pushBlockOperand {ptr : RegionPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_pushBlockOperand {ptr : BlockArgumentPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_pushBlockOperand {ptr : OpResultPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_pushBlockOperand {ptr : OpOperandPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_pushBlockOperand {block : BlockPtr} :
    block.getNumArguments! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    block.getNumArguments! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getFirstUse!_pushBlockOperand {value : ValuePtr} :
    value.getFirstUse! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_pushBlockOperand {value : ValuePtr} :
    value.getType! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    value.getType! ctx := by
  grind

@[grind =]
theorem BlockOperandPtr.get!_pushBlockOperand {operand : BlockOperandPtr} :
    operand.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    if operand = op.nextBlockOperand ctx then
      { value := target, owner := op, back := .blockFirstUse target, nextUse := none }
    else operand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getOperands!_pushBlockOperand {operation : OperationPtr} :
    operation.getOperands! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    operation.getOperands! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtrPtr.get!_pushBlockOperand {ptr : OpOperandPtrPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    ptr.get! ctx := by
  grind

@[grind =]
theorem BlockOperandPtrPtr.get!_pushBlockOperand {ptr : BlockOperandPtrPtr} :
    ptr.get! (Rewriter.pushBlockOperand ctx op target hop htarget) =
    if ptr = .blockOperandNextUse (op.nextBlockOperand ctx) then none else ptr.get! ctx := by
  cases ptr <;> grind

@[grind =]
theorem Rewriter.pushBlockOperand_spec_inBounds (ptr : GenericPtr) :
    ptr.InBounds (Rewriter.pushBlockOperand ctx op target hop htarget) ↔
    (ptr.InBounds ctx ∨
      ptr = .blockOperand (op.nextBlockOperand ctx) ∨
      ptr = .blockOperandPtr (.blockOperandNextUse (op.nextBlockOperand ctx))) := by
  grind

@[grind =]
theorem Rewriter.pushBlockOperand_spec_topLevel_inBounds (ptr : TopLevelPtr) :
    ptr.InBounds (Rewriter.pushBlockOperand ctx op target hop htarget) ↔ ptr.InBounds ctx := by
  grind

@[grind .]
theorem Rewriter.pushBlockOperand_spec_fieldsInBounds (hctx : ctx.FieldsInBounds) :
    (Rewriter.pushBlockOperand ctx op target hop htarget).FieldsInBounds := by
  grind [BlockOperand.FieldsInBounds]

end Rewriter.pushBlockOperand

end Veir
