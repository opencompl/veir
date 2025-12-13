import Mlir.Core.Basic
import Mlir.Core.Fields
import Mlir.Rewriter.LinkedList.Basic

/-
 - The getters we consider are:
 - * IRContext.topLevelOp
 - * BlockPtr.get! optionally replaced by the following special cases:
 -   * Block.firstUse
 -   * Block.prev
 -   * Block.next
 -   * Block.parent
 -   * Block.firstOp
 -   * Block.lastOp
 - * OperationPtr.get! optionally replaced by the following special cases:
 -   * Operation.prev
 -   * Operation.next
 -   * Operation.parent
 -   * Operation.opType
 -   * Operation.attrs
 -   * Operation.properties
 - * OperationPtr.getNumResults!
 - * OpResultPtr.get!
 - * OperationPtr.getNumOperands!
 - * OpOperandPtr.get! optionally replaced by the following special case:
 - * OperationPtr.getNumSuccessors!
 - * BlockOperandPtr.get!
 - * OperationPtr.getNumRegions!
 - * OperationPtr.getRegion!
 - * BlockOperandPtrPtr.get!
 - * BlockPtr.getNumArguments!
 - * BlockArgumentPtr.get!
 - * RegionPtr.get!
 - * ValuePtr.getFirstUse!
 - * ValuePtr.getType!
 - * OpOperandPtrPtr.get!
 -/
namespace Mlir

variable {operation operation' : OperationPtr}
variable {block block' : BlockPtr}
variable {rg rg' : RegionPtr}
variable {opOperand opOperand' : OpOperandPtr}
variable {opOperandPtr opOperandPtr' : OpOperandPtrPtr}
variable {blockOperand blockOperand' : BlockOperandPtr}
variable {value value' : ValuePtr}

/- OpOperandPtr.removeFromCurrent -/
attribute [local grind] OpOperandPtr.removeFromCurrent

@[simp, grind =]
theorem IRContext.topLevelOp_OpOperandPtr_removeFromCurrent :
    (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds).topLevelOp =
    ctx.topLevelOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_removeFromCurrent {block : BlockPtr} :
    (block.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumResults! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtr_removeFromCurrent {opResult : OpResultPtr} :
    opResult.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse (.opResult opResult) then
      { opResult.get! ctx with firstUse := (opOperand'.get! ctx).nextUse }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_removeFromCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    { opOperand.get! ctx with
        back :=
          if (opOperand'.get! ctx).nextUse = some opOperand then
            (opOperand'.get! ctx).back
          else
            (opOperand.get! ctx).back
        nextUse :=
          if (opOperand'.get! ctx).back = .operandNextUse opOperand then
            (opOperand'.get! ctx).nextUse
          else
            (opOperand.get! ctx).nextUse
    } := by
  simp [removeFromCurrent]
  split
  · split
    · grind
    · split
      · grind
      · -- TODO: Why doesn't 'grind' work here?
        simp only [get!_OpOperandPtrPtr_set, ite_eq_right_iff]
        grind
  · split
    · grind
    · split
      · grind
      · simp [OpOperandPtr.get!_OpOperandPtr_setBack]
        split
        · grind
        · simp only [get!_OpOperandPtrPtr_set, ite_eq_right_iff]
          grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_removeFromCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getNumRegions! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_removeFromCurrent {operation : OperationPtr} :
    operation.getRegion! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_removeFromCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.removeFromCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_removeFromCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse (.blockArgument blockArg) then
      { blockArg.get! ctx with firstUse := (opOperand'.get! ctx).nextUse }
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_removeFromCurrent {region : RegionPtr} :
    region.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).back = .valueFirstUse value then
      (opOperand'.get! ctx).nextUse
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_removeFromCurrent {value : ValuePtr} :
    value.getType! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_removeFromCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.removeFromCurrent ctx hopOperand' ctxInBounds) =
    if opOperandPtr = (opOperand'.get! ctx).back then
      (opOperand'.get! ctx).nextUse
    else
      opOperandPtr.get! ctx := by
  grind

/- OpOperandPtr.insertIntoCurrent -/
attribute [local grind] OpOperandPtr.insertIntoCurrent

@[simp, grind =]
theorem IRContext.topLevelOp_OpOperandPtr_insertIntoCurrent :
    (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds).topLevelOp =
    ctx.topLevelOp := by
  grind

@[simp, grind =]
theorem BlockPtr.firstUse!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).firstUse =
    (block.get! ctx).firstUse := by
  grind

@[simp, grind =]
theorem BlockPtr.prev!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).prev =
    (block.get! ctx).prev := by
  grind

@[simp, grind =]
theorem BlockPtr.next!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).next =
    (block.get! ctx).next := by
  grind

@[simp, grind =]
theorem BlockPtr.parent!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).parent =
    (block.get! ctx).parent := by
  grind

@[simp, grind =]
theorem BlockPtr.firstOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).firstOp =
    (block.get! ctx).firstOp := by
  grind

@[simp, grind =]
theorem BlockPtr.lastOp!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} :
    (block.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).lastOp =
    (block.get! ctx).lastOp := by
  grind

@[simp, grind =]
theorem OperationPtr.prev!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).prev =
    (operation.get! ctx).prev := by
  grind

@[simp, grind =]
theorem OperationPtr.next!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).next =
    (operation.get! ctx).next := by
  grind

@[simp, grind =]
theorem OperationPtr.parent!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).parent =
    (operation.get! ctx).parent := by
  grind

@[simp, grind =]
theorem OperationPtr.opType!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).opType =
    (operation.get! ctx).opType := by
  grind

@[simp, grind =]
theorem OperationPtr.attrs!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).attrs =
    (operation.get! ctx).attrs := by
  grind

@[simp, grind =]
theorem OperationPtr.properties!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    (operation.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds)).properties =
    (operation.get! ctx).properties := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumResults! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumResults! ctx := by
  grind

@[grind =]
theorem OpResultPtr.get!_OpOperandPtr_insertIntoCurrent {opResult : OpResultPtr} :
    opResult.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = (.opResult opResult) then
      { opResult.get! ctx with firstUse := opOperand' }
    else
      opResult.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumOperands!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumOperands! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumOperands! ctx := by
  grind

@[grind =]
theorem OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent {opOperand : OpOperandPtr} :
    opOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    { opOperand.get! ctx with
        back :=
          if (opOperand'.get! ctx).value.getFirstUse! ctx = some opOperand then
            .operandNextUse opOperand'
          else if opOperand' = opOperand then
            .valueFirstUse ((opOperand'.get! ctx).value)
          else
            (opOperand.get! ctx).back
        nextUse :=
          if opOperand' = opOperand then
            (opOperand'.get! ctx).value.getFirstUse! ctx
          else
            (opOperand.get! ctx).nextUse
    } := by
  simp only [insertIntoCurrent]
  by_cases h: opOperand = opOperand'
  · grind
  · simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack]
    split
    · rename_i h₁
      simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack] at h₁
      simp only [get!_ValuePtr_setFirstUse]
      simp only [OpOperandPtr.get!_OpOperandPtr_setNextUse, h, ↓reduceIte]
      simp only [get!_OpOperandPtr_setBack, h, ↓reduceIte]
      simp only [Ne.symm h, ↓reduceIte]
      simp only [h₁, reduceCtorEq, ↓reduceIte]
    · rename_i ptr h₁
      simp only [← get!_eq_get, ← ValuePtr.getFirstUse!_eq_getFirstUse, ValuePtr.getFirstUse!_OpOperandPtr_setBack] at h₁
      simp [h₁]
      by_cases heq: ptr = opOperand
      · grind
      · simp only [Ne.symm h, ↓reduceIte, heq]
        simp only [get!_OpOperandPtr_setBack, Ne.symm heq, ↓reduceIte, get!_ValuePtr_setFirstUse]
        simp only [get!_OpOperandPtr_setNextUse, h, ↓reduceIte]
        simp only [get!_OpOperandPtr_setBack]
        simp only [ite_eq_right_iff] -- Why does grind needs these here to work?
        grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumSuccessors! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumSuccessors! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    blockOperand.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    blockOperand.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getNumRegions!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getNumRegions! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getNumRegions! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.getRegion!_OpOperandPtr_insertIntoCurrent {operation : OperationPtr} :
    operation.getRegion! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    operation.getRegion! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {blockOperandPtr : BlockOperandPtrPtr} :
    blockOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.getNumArguments!_OpOperandPtr_insertIntoCurrent {block : BlockPtr} {hop} :
    block.getNumArguments! (opOperand'.insertIntoCurrent ctx newOperands hop) =
    block.getNumArguments! ctx := by
  grind

@[grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_insertIntoCurrent {blockArg : BlockArgumentPtr} :
    blockArg.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = (.blockArgument blockArg) then
      { blockArg.get! ctx with firstUse := opOperand' }
    else
      blockArg.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_insertIntoCurrent {region : RegionPtr} :
    region.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    region.get! ctx := by
  grind

@[grind =]
theorem ValuePtr.getFirstUse!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getFirstUse! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if (opOperand'.get! ctx).value = value then
      some opOperand'
    else
      value.getFirstUse! ctx := by
  grind

@[simp, grind =]
theorem ValuePtr.getType!_OpOperandPtr_insertIntoCurrent {value : ValuePtr} :
    value.getType! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    value.getType! ctx := by
  grind

@[grind =]
theorem OpOperandPtrPtr.get!_OpOperandPtr_insertIntoCurrent {opOperandPtr : OpOperandPtrPtr} :
    opOperandPtr.get! (opOperand'.insertIntoCurrent ctx hopOperand' ctxInBounds) =
    if opOperandPtr = .operandNextUse opOperand' then
      (opOperand'.get! ctx).value.getFirstUse! ctx
    else if opOperandPtr = .valueFirstUse ((opOperand'.get! ctx).value) then
      some opOperand'
    else
      opOperandPtr.get! ctx := by
  grind

@[simp, grind =>]
theorem OperationPtr.get!_OperationPtr_setParentWithCheck
    (heq : operation'.setParentWithCheck ctx parent h' = some newCtx) :
    operation.get! newCtx =
    if operation' = operation then
      { operation.get! ctx with parent := some parent }
    else
      operation.get! ctx
    := by
  unfold OperationPtr.setParentWithCheck at heq
  grind

@[simp, grind =]
theorem OperationPtr.getNumResults_OpOperandPtr_setBack :
    OperationPtr.getNumResults op (OpOperandPtr.setBack operandPtr ctx h₁ v) hop =
    OperationPtr.getNumResults op ctx (by grind) := by
  grind

@[simp, grind =>]
theorem OpOperandPtr.get!_OperationPtr_setParentWithCheck (res : OpOperandPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  grind [OperationPtr.setParentWithCheck]


@[simp, grind =]
theorem ValuePtr.get_OpOperandPtr_pushResult(arg : BlockArgumentPtr)
    (h : arg.InBounds (operation.pushResult ctx newResult hop)) :
    arg.get (operation.pushResult ctx newResult hop) h = arg.get ctx := by
  grind


@[simp, grind =>]
theorem BlockArgumentPtr.get!_OperationPtr_setParentWithCheck (res : BlockArgumentPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get! newCtx = res.get! ctx  := by
  grind [OperationPtr.setParentWithCheck]


@[simp, grind =>]
theorem RegionPtr.get!_OperationPtr_setParentWithCheck (rg : RegionPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    rg.get! newCtx = rg.get! ctx  := by
  grind [OperationPtr.setParentWithCheck]

@[simp, grind =>]
theorem BlockArgumentPtr.get_OperationPtr_setParentWithCheck (res : BlockArgumentPtr) (h : res.InBounds ctx)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get newCtx (by grind) = res.get ctx := by
  grind [OperationPtr.setParentWithCheck]


@[simp, grind =>]
theorem OpResultPtr.get!_OperationPtr_setParentWithCheck (res : OpResultPtr)
    (heq : operation.setParentWithCheck ctx h' newNext = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  grind [OperationPtr.setParentWithCheck]


variable (ctx : IRContext)
variable (ctxInBounds : ctx.FieldsInBounds)

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setBack_results_size (op : OperationPtr):
    op.getNumResults! (OpOperandPtr.setBack operandPtr ctx h newBack) = op.getNumResults! ctx := by
  grind [OpOperandPtr.setBack]

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setNextUse_results_size (op : OperationPtr):
    op.getNumResults! (OpOperandPtr.setNextUse operandPtr ctx h newNextUse) = op.getNumResults! ctx := by
  grind [OpOperandPtr.setNextUse]

@[simp, grind .]
theorem OperationPtr.get!_ValuePtr_setFirstUse_results_size (op : OperationPtr) :
    op.getNumResults! (ValuePtr.setFirstUse val ctx h newFirstUse) = op.getNumResults! ctx := by
  cases val <;> grind [ValuePtr.setFirstUse]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setBack_operands_size (op : OperationPtr) :
    op.getNumOperands! (OpOperandPtr.setBack operandPtr ctx h₁ v) =
    op.getNumOperands! ctx := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setNextUse_operands_size (op : OperationPtr) :
    op.getNumOperands! (OpOperandPtr.setNextUse operandPtr ctx h₁ v) =
    op.getNumOperands! ctx := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setFirstUse_operands_size (op : OperationPtr) :
    op.getNumOperands! (ValuePtr.setFirstUse valuePtr ctx h₁ v) =
    op.getNumOperands! ctx := by
  cases valuePtr <;> grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setBack_operands_owner (opr : OpOperandPtr) :
    (opr.get! (OpOperandPtr.setBack operandPtr ctx h₁ v)).owner =
    (opr.get! ctx).owner := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setNextUse_operands_owner (opr : OpOperandPtr) :
    (opr.get! (OpOperandPtr.setNextUse operandPtr ctx h₁ v)).owner =
    (opr.get! ctx).owner := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setFirstUse_operands_owner (opr : OpOperandPtr) :
    (opr.get! (ValuePtr.setFirstUse valuePtr ctx h₁ v)).owner =
    (opr.get! ctx).owner := by
  cases valuePtr <;> grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpResultPtr.get!_OpOperandPtr_linkBetween (res : OpResultPtr) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.get! (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) = res.get! ctx := by
  unfold OperationPtr.linkBetween
  simp
  split
  · split <;> grind
  · grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_OpOperandPtr_linkBetween (res : BlockArgumentPtr) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.get! (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) = res.get! ctx := by
  unfold OperationPtr.linkBetween
  simp
  split
  · split <;> grind
  · grind

@[simp, grind =]
theorem ValuePtr.get!_OpOperandPtr_linkBetween (res : ValuePtr) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.getFirstUse! (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) = res.getFirstUse! ctx := by
  cases res <;> grind [getFirstUse!]

@[simp, grind =]
theorem OpOperandPtr.get!_OpOperandPtr_linkBetween (res : OpOperandPtr) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.get! (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) = res.get! ctx := by
  unfold OperationPtr.linkBetween
  simp
  split
  · split <;> grind
  · grind

@[simp, grind =>]
theorem OpResultPtr.get!_OpOperandPtr_linkBetweenWithParent (res : OpResultPtr) (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  unfold OperationPtr.linkBetweenWithParent at heq
  grind

@[simp, grind =>]
theorem BlockArgumentPtr.get!_OpOperandPtr_linkBetweenWithParent (res : BlockArgumentPtr)  (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  unfold OperationPtr.linkBetweenWithParent at heq
  grind

@[simp, grind =>]
theorem ValuePtr.get!_OpOperandPtr_linkBetweenWithParent (res : ValuePtr)  (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.getFirstUse! newCtx = res.getFirstUse! ctx := by
  cases res <;> grind [getFirstUse!]

@[simp, grind =>]
theorem OpOperandPtr.get!_OpOperandPtr_linkBetweenWithParent (res : OpOperandPtr) (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.get! newCtx = res.get! ctx := by
  unfold OperationPtr.linkBetweenWithParent at heq
  grind

@[simp, grind =]
theorem OpResultPtr.get_OpOperandPtr_linkBetween (res : OpResultPtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.get (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) (by grind) = res.get ctx h := by
  have := @get!_OpOperandPtr_linkBetween ctx prevOp nextOp h₂ h₃ res
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get_OpOperandPtr_linkBetween (res : BlockArgumentPtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.get (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) (by grind) = res.get ctx h := by
  have := @get!_OpOperandPtr_linkBetween ctx prevOp nextOp h₂ h₃ res
  grind

@[simp, grind =]
theorem ValuePtr.get_OpOperandPtr_linkBetween (res : ValuePtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.getFirstUse (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) (by grind) = res.getFirstUse ctx h := by
  have := @get!_OpOperandPtr_linkBetween ctx prevOp nextOp h₂ h₃ res
  grind

@[simp, grind =]
theorem OpOperandPtr.get_OpOperandPtr_linkBetween (res : OpOperandPtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx) :
    res.get (op.linkBetween ctx prevOp nextOp h₁ h₂ h₃) (by grind) = res.get ctx h := by
  have := @get!_OpOperandPtr_linkBetween ctx prevOp nextOp h₂ h₃ res
  grind

@[simp, grind =]
theorem OperationPtr.getParent_OperationPtr_linkBetween :
    (OperationPtr.get op (OperationPtr.linkBetween op' ctx prevOp nextOp h₁ h₂ h₃) hop).parent =
      (OperationPtr.get op ctx (by grind)).parent := by
  unfold OperationPtr.linkBetween
  grind

@[simp, grind =>]
theorem OpResultPtr.get_OpOperandPtr_linkBetweenWithParent (res : OpResultPtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.get newCtx (by grind) = res.get ctx h := by
  have := get!_OpOperandPtr_linkBetweenWithParent (heq := heq)
  grind


@[simp, grind =>]
theorem BlockArgumentPtr.get_OpOperandPtr_linkBetweenWithParent (res : BlockArgumentPtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.get newCtx (by grind) = res.get ctx h := by
  have := get!_OpOperandPtr_linkBetweenWithParent (heq := heq) (res := res)
  grind

@[simp, grind =>]
theorem ValuePtr.get_OpOperandPtr_linkBetweenWithParent (res : ValuePtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.getFirstUse newCtx (by grind) = res.getFirstUse ctx h := by
  have := get!_OpOperandPtr_linkBetweenWithParent (heq := heq) (res := res)
  grind

@[simp, grind =>]
theorem OpOperandPtr.get_OpOperandPtr_linkBetweenWithParent (res : OpOperandPtr) (h : res.InBounds ctx) (op : OperationPtr) (h₁ : op.InBounds ctx)
    (heq : op.linkBetweenWithParent ctx prevOp nextOp parent hp h₁ h₂ h₃ = some newCtx) :
    res.get newCtx (by grind) = res.get ctx h := by
  have := get!_OpOperandPtr_linkBetweenWithParent (heq := heq) (res := res)
  grind
