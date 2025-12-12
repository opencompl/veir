import Mlir.Core.Basic
import Mlir.Core.Fields
import Mlir.Rewriter.LinkedList.Basic

namespace Mlir

variable {operation operation' : OperationPtr}
variable {block block' : BlockPtr}
variable {rg rg' : RegionPtr}
variable {opOperand opOperand' : OpOperandPtr}
variable {opOperandPtr opOperandPtr' : OpOperandPtrPtr}
variable {blockOperand blockOperand' : BlockOperandPtr}
variable {value value' : ValuePtr}


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

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_ValuePtr_InBounds_iff (operandPtr : OpOperandPtr) (operandPtrInBounds : operandPtr.InBounds ctx) :
    ∀ (valuePtr : ValuePtr), (valuePtr.InBounds (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds)) ↔ (valuePtr.InBounds ctx) := by
  grind [OpOperandPtr.insertIntoCurrent]

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


@[grind .]
theorem OperationPtr.get!_OpOperandPtr_insertIntoCurrent_results_size (op : OperationPtr) :
    op.getNumResults! (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) = op.getNumResults! ctx := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;>
    simp only [OperationPtr.get!_ValuePtr_setFirstUse_results_size, OperationPtr.get!_OpOperandPtr_setNextUse_results_size, OperationPtr.get!_OpOperandPtr_setBack_results_size]

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_preserves_parent (op : OperationPtr) :
    (op.get! (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂)).parent = (op.get! ctx).parent := by
  simp only [insertIntoCurrent]
  split <;> simp

@[simp, grind =]
theorem OperationPtr.getNumResults_insertIntoCurrent :
    OperationPtr.getNumResults! op (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) =
    OperationPtr.getNumResults! op ctx := by
  simp only [OpOperandPtr.insertIntoCurrent]
  grind

@[simp, grind =]
theorem OpResultPtr.owner_insertIntoCurrent :
    (OpResultPtr.get opr (OpOperandPtr.insertIntoCurrent ctx use h₁ h₂) hopr).owner =
    (OpResultPtr.get opr ctx (by grind)).owner := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind =]
theorem OpResultPtr.index_insertIntoCurrent :
    (OpResultPtr.get opr (OpOperandPtr.insertIntoCurrent ctx use h₁ h₂) hopr).index =
    (OpResultPtr.get opr ctx (by grind)).index := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind =]
theorem OperationPtr.getNumOperands_insertIntoCurrent :
    OperationPtr.getNumOperands op (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) hop =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind =]
theorem OpOperandPtr.owner_insertIntoCurrent :
    (OpOperandPtr.get opr (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) hopr).owner =
    (OpOperandPtr.get opr ctx (by grind)).owner := by
  simp only [OpOperandPtr.insertIntoCurrent, ←OpOperandPtr.get!_eq_get]
  split <;> grind (gen := 20)

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_insertIntoCurrent :
    OperationPtr.getNumSuccessors! op (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) =
    OperationPtr.getNumSuccessors! op ctx := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind =]
theorem BlockOperandPtr.get!_insertIntoCurrent {blockOperand : BlockOperandPtr} :
    (blockOperand.get! (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂)) =
    (blockOperand.get! ctx) := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind .]
theorem RegionPtr.get!_OpOperandPtr_insertIntoCurrent (r : RegionPtr) :
    r.get! (OpOperandPtr.insertIntoCurrent ctx opr h₁ h₂) = r.get! ctx := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind .]
theorem RegionPtr.get_OpOperandPtr_insertIntoCurrent (r : RegionPtr) (h₃ : r.InBounds ctx) :
    r.get (OpOperandPtr.insertIntoCurrent ctx opr h₁ h₂) = r.get ctx h₃ := by
  simp only [← get!_eq_get, get!_OpOperandPtr_insertIntoCurrent]

@[simp, grind =]
theorem RegionPtr.get!_OpOperandPtr_removeFromCurrent (r : RegionPtr) :
    r.get! (OpOperandPtr.removeFromCurrent ctx opr h₁ h₂) = r.get! ctx := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem RegionPtr.get_OpOperandPtr_removeFromCurrent (r : RegionPtr) (h : r.InBounds ctx) :
    r.get (OpOperandPtr.removeFromCurrent ctx opr h₁ h₂) = r.get ctx h := by
  simp only [← get!_eq_get, get!_OpOperandPtr_removeFromCurrent]

theorem OpOperandPtr.insertIntoCurrent_ValuePtr_getFirstUse! (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx) :
      ∀ valuePtr, ValuePtr.getFirstUse! valuePtr (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
        if valuePtr = (operandPtr.get! ctx).value then
          (some operandPtr)
        else
          valuePtr.getFirstUse! ctx := by
  grind [insertIntoCurrent]

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_ValuePtr_getFirstUse (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx) :
      ∀ valuePtr valuePtrIn, ValuePtr.getFirstUse valuePtr (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) valuePtrIn =
        if valuePtr = (operandPtr.get ctx (by grind)).value then
          some operandPtr
        else
          valuePtr.getFirstUse ctx (by grind) := by
  intros valuePtr hval
  have h := insertIntoCurrent_ValuePtr_getFirstUse! ctx ctxInBounds operandPtr operandPtrInBounds valuePtr
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_insertIntoCurrent {operand operand' : OpOperandPtr}
    (hoper : operand.InBounds ctx) (hoper' : operand'.InBounds ctx) (hx : ctx.FieldsInBounds)
    (h : (operand.get ctx).value.getFirstUse ctx ≠ some operand) :
    operand'.get! (operand.insertIntoCurrent ctx hoper hx) =
      if _ : operand' = operand then
        { operand.get ctx with nextUse := (operand.get ctx).value.getFirstUse ctx, back := OpOperandPtrPtr.valueFirstUse (operand.get ctx).value }
      else if _ : some operand' = (operand.get ctx).value.getFirstUse ctx then
        { operand'.get ctx with  back := OpOperandPtrPtr.operandNextUse operand }
      else
        operand'.get! ctx
     := by
  grind [insertIntoCurrent]

@[simp, grind =]
theorem OpOperandPtr.BlockOperand_get_insertIntoCurrent
    (operandPtr : OpOperandPtr) (blockOperandPtr : BlockOperandPtr) (operandPtrInBounds ctxInBounds blockInBounds):
      blockOperandPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) blockInBounds = blockOperandPtr.get ctx (by grind) := by
  simp only [insertIntoCurrent, ←BlockOperandPtr.get!_eq_get]
  split <;> simp <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_BlockPtr_get_firstUse_mono (blockPtr : BlockPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (blockPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).firstUse =
      (blockPtr.get ctx (by grind)).firstUse := by
  simp only [←BlockPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_BlockPtr_get_firstOp_mono (blockPtr : BlockPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (blockPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).firstOp =
      (blockPtr.get ctx (by grind)).firstOp := by
  simp only [←BlockPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_BlockPtr_get_lastOp_mono (blockPtr : BlockPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (blockPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).lastOp =
      (blockPtr.get ctx (by grind)).lastOp := by
  simp only [←BlockPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_BlockPtr_get_next_mono {blockPtr : BlockPtr} {hInBounds} :
    (blockPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).next =
      (blockPtr.get ctx (by grind)).next := by
  simp only [←BlockPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_BlockPtr_get_prev_mono {blockPtr : BlockPtr} {hInBounds} :
    (blockPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).prev =
      (blockPtr.get ctx (by grind)).prev := by
  simp only [←BlockPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_BlockPtr_get_parent_mono (blockPtr : BlockPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (blockPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).parent =
      (blockPtr.get ctx (by grind)).parent := by
  simp only [←BlockPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_parent_mono (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) opInBounds :
    (opPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) opInBounds).parent =
      (opPtr.get ctx (by grind)).parent := by
  simp only [←OperationPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get!_regions (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    opPtr.getRegion! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
      opPtr.getRegion! ctx := by
  grind [OpOperandPtr.insertIntoCurrent]

@[grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_parent (bl : BlockPtr) (h : bl.InBounds ctx) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).parent = (bl.get! ctx).parent := by
  simp only [insertIntoCurrent]
  grind

@[grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_prev (bl : BlockPtr) (h : bl.InBounds ctx) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).prev = (bl.get! ctx).prev := by
  simp only [insertIntoCurrent]
  grind

@[grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_next (bl : BlockPtr) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).next = (bl.get! ctx).next := by
  simp only [insertIntoCurrent]
  grind

@[grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_size (bl : BlockPtr):
    bl.getNumArguments! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds) = bl.getNumArguments! ctx := by
  simp only [insertIntoCurrent]
  grind

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_index (ba : BlockArgumentPtr):
    (ba.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).index = (ba.get! ctx).index := by
  grind [insertIntoCurrent]

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_owner (ba : BlockArgumentPtr):
    (ba.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).owner = (ba.get! ctx).owner := by
  grind [insertIntoCurrent]

@[simp, grind =]
theorem OpOperandPtr.RegionPtr_get!_pushOperand (rg : RegionPtr) :
    rg.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds) = rg.get! ctx := by
  simp only [insertIntoCurrent]
  grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_next_mono (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (opPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).next =
      (opPtr.get ctx (by grind)).next := by
  simp only [←OperationPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_prev_mono (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (opPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).prev =
      (opPtr.get ctx (by grind)).prev := by
  simp only [←OperationPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_regions! (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    opPtr.getRegion! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
      opPtr.getRegion! ctx := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_RegionPtr_get (rgPtr : RegionPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (rgPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds) =
      (rgPtr.get ctx (by grind)) := by
  simp only [←RegionPtr.get!_eq_get]
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

@[simp, grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_num_results (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    opPtr.getNumResults! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) =
    opPtr.getNumResults! ctx := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

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
theorem OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_size (op : OperationPtr) :
    op.getNumOperands! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds) =
    op.getNumOperands! ctx := by
  simp only [insertIntoCurrent]
  split <;> simp only [OpOperandPtr.OperationPtr_get!_setFirstUse_operands_size,
      OpOperandPtr.OperationPtr_get!_setNextUse_operands_size,
      OpOperandPtr.OperationPtr_get!_setBack_operands_size]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get_insertIntoCurrent_operands_size (op : OperationPtr)
    (h : op.InBounds ctx) :
    op.getNumOperands! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds) =
    op.getNumOperands! ctx := by
  have := @OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_size ctx ctxInBounds operandPtr h₁ op
  grind

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
theorem OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_owner (opr : OpOperandPtr) :
    (opr.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).owner =
    (opr.get! ctx).owner := by
  simp only [insertIntoCurrent]
  split <;> simp only [OpOperandPtr.OperationPtr_get!_setFirstUse_operands_owner,
      OpOperandPtr.OperationPtr_get!_setNextUse_operands_owner,
      OpOperandPtr.OperationPtr_get!_setBack_operands_owner]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get_insertIntoCurrent_operands_owner (opr : OpOperandPtr) :
    (opr.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).owner =
    (opr.get! ctx).owner := by
  have := @OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_owner ctx ctxInBounds operandPtr h₁ opr
  grind


@[simp, grind =]
theorem OpOperandPtr.OpOperandPtr_getValue!_insertIntoCurrent (opd : OpOperandPtr)
    (operandPtr : OpOperandPtr) (hopd : opd.InBounds ctx) (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    (opd.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds)).value =
      (opd.get! ctx).value := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtr.OpOperandPtr_getValue_insertIntoCurrent (opd : OpOperandPtr)
    (operandPtr : OpOperandPtr) (hopd : opd.InBounds ctx) (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) h :
    (opd.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) h).value =
      (opd.get ctx (by grind)).value := by
  have := OpOperandPtr.OpOperandPtr_getValue!_insertIntoCurrent ctx opd operandPtr hopd operandPtrInBounds ctxInBounds
  grind

theorem OpOperandPtr.OpOperandPtr_getBack!_insertIntoCurrent (opd : OpOperandPtr)
    (newUse : OpOperandPtr) (hopd : opd.InBounds ctx) (newUseInBounds : newUse.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    (opd.get! (OpOperandPtr.insertIntoCurrent ctx newUse newUseInBounds ctxInBounds)).back =
    if (newUse.get! ctx).value.getFirstUse! ctx = opd then
      OpOperandPtrPtr.operandNextUse newUse
    else if newUse = opd then
      OpOperandPtrPtr.valueFirstUse (newUse.get ctx newUseInBounds).value
    else
      (opd.get! ctx).back
    := by
  unfold insertIntoCurrent
  split
  · simp
    split <;> grind
  · simp
    split <;> grind (gen := 20)

@[simp, grind =]
theorem OpOperandPtr.OpOperandPtr_getBack_insertIntoCurrent (opd : OpOperandPtr)
    (newUse : OpOperandPtr) (newUseInBounds : newUse.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) h :
    (opd.get (OpOperandPtr.insertIntoCurrent ctx newUse newUseInBounds ctxInBounds) h).back =
    if (newUse.get ctx (by grind)).value.getFirstUse ctx = some opd then
      (OpOperandPtrPtr.operandNextUse newUse)
    else if newUse = opd then
      (OpOperandPtrPtr.valueFirstUse (newUse.get ctx newUseInBounds).value)
    else
      (opd.get ctx (by grind)).back := by
  have := OpOperandPtr.OpOperandPtr_getBack!_insertIntoCurrent ctx opd newUse
  grind

@[simp, grind =]
theorem OpOperandPtr.OpOperandPtr_getNext!_insertIntoCurrent (opd : OpOperandPtr)
    (newUse : OpOperandPtr) (hop : opd.InBounds ctx) (newUseInBounds : newUse.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    (opd.get! (OpOperandPtr.insertIntoCurrent ctx newUse newUseInBounds ctxInBounds)).nextUse =
    if opd = newUse then
      (newUse.get! ctx).value.getFirstUse! ctx
    else
      (opd.get! ctx).nextUse := by
  simp only [insertIntoCurrent]
  split <;> grind (gen := 20)

theorem OpOperandPtr.OpOperandPtr_getNext_insertIntoCurrent (opd : OpOperandPtr)
    (newUse : OpOperandPtr) (newUseInBounds : newUse.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) h :
    (opd.get (OpOperandPtr.insertIntoCurrent ctx newUse newUseInBounds ctxInBounds) h).nextUse =
    if opd = newUse then
      (newUse.get ctx (by grind)).value.getFirstUse ctx
    else
      (opd.get ctx (by grind)).nextUse := by
  have := OpOperandPtr.OpOperandPtr_getNext!_insertIntoCurrent ctx opd newUse
  grind

@[simp, grind .]
theorem OpOperandPtr.removeFromCurrent_preserves_results_size' (op : OperationPtr) :
    op.getNumResults! (OpOperandPtr.removeFromCurrent ctx ptr h₁ h₂) = op.getNumResults! ctx := by
  simp [removeFromCurrent]
  split <;> simp

@[simp, grind .]
theorem OpOperandPtr.removeFromCurrent_preserves_parent (op : OperationPtr) :
    (op.get! (OpOperandPtr.removeFromCurrent ctx ptr h₁ h₂)).parent = (op.get! ctx).parent := by
  simp [removeFromCurrent]
  split <;> simp <;> grind (gen := 20) [cases ValuePtr]

@[grind =]
theorem OpOperandPtr.removeFromCurrent_OpOperandPtr_get_back
    (use : OpOperandPtr) (operandPtr : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) operandPtrInBounds :
    (operandPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) operandPtrInBounds).back =
    (if (use.get ctx (by grind)).nextUse = some operandPtr then
      (use.get ctx (by grind)).back
    else
      (operandPtr.get ctx (by grind)).back) := by
  grind [removeFromCurrent]

@[grind =]
theorem OpOperandPtr.removeFromCurrent_OpOperandPtr_get_nextUse
    (use : OpOperandPtr) (operandPtr : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) operandPtrInBounds :
    (operandPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) operandPtrInBounds).nextUse =
    if (use.get ctx (by grind)).back = OpOperandPtrPtr.operandNextUse operandPtr then
      (use.get ctx (by grind)).nextUse
    else
      (operandPtr.get ctx (by grind)).nextUse := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_OpOperandPtr_get_value
    (use : OpOperandPtr) (operandPtr : OpOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) operandPtrInBounds :
    (operandPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) operandPtrInBounds).value =
    (operandPtr.get ctx (by grind)).value := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_BlockPtr_getFirstUse
    (use : OpOperandPtr) (blockPtr : BlockPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) blockPtrInBounds :
    (blockPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) blockPtrInBounds).firstUse =
    (blockPtr.get ctx (by grind)).firstUse := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_BlockPtr_get_firstOp
    (use : OpOperandPtr) (blockPtr : BlockPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) blockPtrInBounds :
    (blockPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) blockPtrInBounds).firstOp =
    (blockPtr.get ctx (by grind)).firstOp := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_BlockPtr_get_lastOp
    (use : OpOperandPtr) (blockPtr : BlockPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) blockPtrInBounds :
    (blockPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) blockPtrInBounds).lastOp =
    (blockPtr.get ctx (by grind)).lastOp := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_BlockOperandPtr_get
    (use : OpOperandPtr) (blockOperandPtr : BlockOperandPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    blockOperandPtr.get! (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) =
    blockOperandPtr.get! ctx := by
  -- TODO: add lemmas
  unfold removeFromCurrent
  grind

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_OperationPtr_get_parent
    (use : OpOperandPtr) (opPtr : OperationPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) opPtrInBounds :
    (opPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) opPtrInBounds).parent =
    (opPtr.get ctx (by grind)).parent := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_OperationPtr_get_next
    (use : OpOperandPtr) (opPtr : OperationPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) opPtrInBounds :
    (opPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) opPtrInBounds).next =
    (opPtr.get ctx (by grind)).next := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem OpOperandPtr.removeFromCurrent_OperationPtr_get_prev
    (use : OpOperandPtr) (opPtr : OperationPtr) (useInBounds : use.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) opPtrInBounds :
    (opPtr.get (OpOperandPtr.removeFromCurrent ctx use useInBounds ctxInBounds) opPtrInBounds).prev =
    (opPtr.get ctx (by grind)).prev := by
  grind [removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getNext_removeFromCurrent {bl : BlockPtr} h₃ :
    (bl.get (OpOperandPtr.removeFromCurrent ctx ptr h₁ h₂) h₃).next =
      (bl.get ctx (by grind)).next := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getPrev_removeFromCurrent {bl : BlockPtr} h₃ :
    (bl.get (OpOperandPtr.removeFromCurrent ctx ptr h₁ h₂) h₃).prev =
      (bl.get ctx (by grind)).prev := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getParent_removeFromCurrent {bl : BlockPtr} h₃ :
    (bl.get (OpOperandPtr.removeFromCurrent ctx ptr h₁ h₂) h₃).parent =
      (bl.get ctx (by grind)).parent := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem RegionPtr.get_removeFromCurrent {rg : RegionPtr} h₃ :
    rg.get (OpOperandPtr.removeFromCurrent ctx ptr h₁ h₂) h₃ =
      rg.get ctx (by grind) := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumOperands_removeFromCurrent :
    OperationPtr.getNumOperands op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hop =
    OperationPtr.getNumOperands op ctx (by grind) := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getOperandOwner_removeFromCurrent :
    (OpOperandPtr.get opr (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hop).owner =
    (OpOperandPtr.get opr ctx (by grind)).owner := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_removeFromCurrent :
    OperationPtr.getNumSuccessors! op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) =
    OperationPtr.getNumSuccessors! op ctx := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockOperandPtr.get!_removeFromCurrent {blockOpr : BlockOperandPtr} :
    (blockOpr.get! (OpOperandPtr.removeFromCurrent ctx use h₁ h₂)) =
    (blockOpr.get! ctx) := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getNumResults_removeFromCurrent :
    OperationPtr.getNumResults! op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) =
    OperationPtr.getNumResults! op ctx := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OpResultPtr.owner_removeFromCurrent :
    (OpResultPtr.get opr (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hopr).owner =
    (OpResultPtr.get opr ctx (by grind)).owner := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OpResultPtr.index_removeFromCurrent :
    (OpResultPtr.get opr (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hopr).index =
    (OpResultPtr.get opr ctx (by grind)).index := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getRegion!_removeFromCurrent :
    OperationPtr.getRegion! op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) =
    OperationPtr.getRegion! op ctx := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getNumArguments!_removeFromCurrent :
    BlockPtr.getNumArguments! block (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) =
    BlockPtr.getNumArguments! block ctx := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockArgumentPtr.index!_removeFromCurrent {ba : BlockArgumentPtr} :
    (ba.get! (OpOperandPtr.removeFromCurrent ctx use h₁ h₂)).index =
    (ba.get! ctx).index := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockArgumentPtr.owner!_removeFromCurrent {ba : BlockArgumentPtr} :
    (ba.get! (OpOperandPtr.removeFromCurrent ctx use h₁ h₂)).owner =
    (ba.get! ctx).owner := by
  grind [OpOperandPtr.removeFromCurrent]

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
