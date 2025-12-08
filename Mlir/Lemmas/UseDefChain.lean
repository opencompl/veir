import Mlir.UseDefChain
import Mlir.Lemmas.GetSet
import Mlir.Core.Fields

namespace Mlir

-- set_option debug.skipKernelTC true

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

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setBack_blockOperands (op : OperationPtr):
  (op.get! (OpOperandPtr.setBack operandPtr ctx h newBack)).blockOperands = (op.get! ctx).blockOperands := by
  grind [OpOperandPtr.setBack]

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setNextUse_blockOperands (op : OperationPtr):
  (op.get! (OpOperandPtr.setNextUse operandPtr ctx h newNextUse)).blockOperands = (op.get! ctx).blockOperands := by
  grind [OpOperandPtr.setNextUse]

@[simp, grind .]
theorem OperationPtr.get!_ValuePtr_setFirstUse_blockOperands (op : OperationPtr) :
  (op.get! (ValuePtr.setFirstUse val ctx h newFirstUse)).blockOperands = (op.get! ctx).blockOperands := by
  cases val <;> grind [ValuePtr.setFirstUse]

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setBack_parent (op : OperationPtr):
    (op.get! (OpOperandPtr.setBack operandPtr ctx h newBack)).parent = (op.get! ctx).parent := by
  grind [OpOperandPtr.setBack]

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setNextUse_parent (op : OperationPtr):
    (op.get! (OpOperandPtr.setNextUse operandPtr ctx h newNextUse)).parent = (op.get! ctx).parent := by
  grind [OpOperandPtr.setNextUse]

@[simp, grind .]
theorem OperationPtr.get!_ValuePtr_setFirstUse_parent (op : OperationPtr) :
    (op.get! (ValuePtr.setFirstUse val ctx h newFirstUse)).parent = (op.get! ctx).parent := by
  cases val <;> grind [ValuePtr.setFirstUse]

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setBack_regions (op : OperationPtr):
  (op.get! (OpOperandPtr.setBack operandPtr ctx h newBack)).regions = (op.get! ctx).regions := by
  grind [OpOperandPtr.setBack]

@[simp, grind .]
theorem OperationPtr.get!_OpOperandPtr_setNextUse_regions (op : OperationPtr):
  (op.get! (OpOperandPtr.setNextUse operandPtr ctx h newNextUse)).regions = (op.get! ctx).regions := by
  grind [OpOperandPtr.setNextUse]

@[simp, grind .]
theorem OperationPtr.get!_ValuePtr_setFirstUse_regions (op : OperationPtr) :
  (op.get! (ValuePtr.setFirstUse val ctx h newFirstUse)).regions = (op.get! ctx).regions := by
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
  split <;>
    simp only [OperationPtr.get!_ValuePtr_setFirstUse_parent, OperationPtr.get!_OpOperandPtr_setNextUse_parent, OperationPtr.get!_OpOperandPtr_setBack_parent]

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
    (OperationPtr.get op (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) hop).operands.size =
    (OperationPtr.get op ctx (by grind)).operands.size := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind =]
theorem OperationPtr.getOperandOwner_insertIntoCurrent {i : Nat} {hi} :
    ((OperationPtr.get op (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) hop).operands[i]'(hi)).owner =
    ((OperationPtr.get op ctx (by grind)).operands[i]'(by grind)).owner := by
  grind [OpOperandPtr.insertIntoCurrent]

@[simp, grind =]
theorem OperationPtr.getBlockOperands_insertIntoCurrent :
    (OperationPtr.get op (OpOperandPtr.insertIntoCurrent ctx ptr h₁ h₂) hopnd).blockOperands =
    (OperationPtr.get op ctx (by grind)).blockOperands := by
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
    (opPtr.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds)).regions =
      (opPtr.get! ctx).regions := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;>
    simp only [OperationPtr.get!_ValuePtr_setFirstUse_regions, OperationPtr.get!_OpOperandPtr_setNextUse_regions, OperationPtr.get!_OpOperandPtr_setBack_regions]


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
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_next (bl : BlockPtr) (h : bl.InBounds ctx) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).next = (bl.get! ctx).next := by
  simp only [insertIntoCurrent]
  grind

@[grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_size (bl : BlockPtr) (h : bl.InBounds ctx) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).arguments.size = (bl.get! ctx).arguments.size := by
  simp only [insertIntoCurrent]
  grind

@[grind =]
theorem OpOperandPtr.BlockPtr_get_insertIntoCurrent_arguments_size (bl : BlockPtr) (h : bl.InBounds ctx) :
    (bl.get (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).arguments.size = (bl.get ctx).arguments.size := by
  have := OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_size
  grind

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_index (bl : BlockPtr) (i : Nat) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).arguments[i]!.index =
    (bl.get! ctx).arguments[i]!.index := by
  simp only [insertIntoCurrent]
  split
  · simp only [BlockPtr.get!_ValuePtr_setFirstUse, BlockPtr.get!_OpOperandPtr_setNextUse, BlockPtr.get!_OpOperandPtr_setBack]
    split
    · grind
    · split <;> grind [BlockPtr.get!, BlockArgumentPtr.get]
  · grind [BlockPtr.get!, BlockArgumentPtr.get]

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_owner (bl : BlockPtr) (i : Nat) :
    (bl.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).arguments[i]!.owner =
    (bl.get! ctx).arguments[i]!.owner := by
  simp only [insertIntoCurrent]
  split
  · simp only [BlockPtr.get!_ValuePtr_setFirstUse, BlockPtr.get!_OpOperandPtr_setNextUse, BlockPtr.get!_OpOperandPtr_setBack]
    split
    · grind
    · split <;> grind [BlockPtr.get!, BlockArgumentPtr.get]
  · grind [BlockPtr.get!, BlockArgumentPtr.get]

@[grind =]
theorem OpOperandPtr.BlockPtr_get_insertIntoCurrent_arguments_index (bl : BlockPtr) (i : Nat) (h : bl.InBounds ctx) (hi : i < (bl.get ctx h).arguments.size) :
    ((bl.get (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).arguments[i]'(by grind)).index =
    ((bl.get ctx h).arguments[i]'hi).index := by
  have := @OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_index ctx (by grind) operandPtr h₁ bl i
  grind

@[grind =]
theorem OpOperandPtr.BlockPtr_get_insertIntoCurrent_arguments_owner (bl : BlockPtr) (i : Nat) (h : bl.InBounds ctx) (hi : i < (bl.get ctx h).arguments.size) :
    ((bl.get (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).arguments[i]'(by grind)).owner =
    ((bl.get ctx h).arguments[i]'hi).owner := by
  have := @OpOperandPtr.BlockPtr_get!_insertIntoCurrent_arguments_owner ctx (by grind) operandPtr h₁ bl i
  grind

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
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get!_blockOperands (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    (opPtr.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds)).blockOperands =
      (opPtr.get! ctx).blockOperands := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;>
    simp only [OperationPtr.get!_ValuePtr_setFirstUse_blockOperands, OperationPtr.get!_OpOperandPtr_setNextUse_blockOperands,
      OperationPtr.get!_OpOperandPtr_setBack_blockOperands]

@[grind =]
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_blockOperands (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (opPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).blockOperands =
      (opPtr.get ctx (by grind)).blockOperands := by
  have := OpOperandPtr.insertIntoCurrent_OperationPtr_get!_blockOperands
  have := OperationPtr.get!_eq_get hInBounds
  grind

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
theorem OpOperandPtr.insertIntoCurrent_OperationPtr_get_regions (opPtr : OperationPtr) (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) hInBounds :
    (opPtr.get (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds) hInBounds).regions =
      (opPtr.get ctx (by grind)).regions := by
  simp only [←OperationPtr.get!_eq_get]
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
    (op.get! (OpOperandPtr.setBack operandPtr ctx h₁ v)).operands.size =
    (op.get! ctx).operands.size := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setNextUse_operands_size (op : OperationPtr) :
    (op.get! (OpOperandPtr.setNextUse operandPtr ctx h₁ v)).operands.size =
    (op.get! ctx).operands.size := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setFirstUse_operands_size (op : OperationPtr) :
    (op.get! (ValuePtr.setFirstUse valuePtr ctx h₁ v)).operands.size =
    (op.get! ctx).operands.size := by
  cases valuePtr <;> grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_size (op : OperationPtr) :
    (op.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).operands.size =
    (op.get! ctx).operands.size := by
  simp only [insertIntoCurrent]
  split <;> simp only [OpOperandPtr.OperationPtr_get!_setFirstUse_operands_size,
      OpOperandPtr.OperationPtr_get!_setNextUse_operands_size,
      OpOperandPtr.OperationPtr_get!_setBack_operands_size]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get_insertIntoCurrent_operands_size (op : OperationPtr)
    (h : op.InBounds ctx) :
    (op.get (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).operands.size =
    (op.get ctx).operands.size := by
  have := @OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_size ctx ctxInBounds operandPtr h₁ op
  grind

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setBack_operands_owner (op : OperationPtr) (i : Nat) :
    (op.get! (OpOperandPtr.setBack operandPtr ctx h₁ v)).operands[i]!.owner =
    (op.get! ctx).operands[i]!.owner := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setNextUse_operands_owner (op : OperationPtr) (i : Nat) :
    (op.get! (OpOperandPtr.setNextUse operandPtr ctx h₁ v)).operands[i]!.owner =
    (op.get! ctx).operands[i]!.owner := by
  grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_setFirstUse_operands_owner (op : OperationPtr) (i : Nat) :
    (op.get! (ValuePtr.setFirstUse valuePtr ctx h₁ v)).operands[i]!.owner =
    (op.get! ctx).operands[i]!.owner := by
  cases valuePtr <;> grind [OpOperandPtr.get, OperationPtr.get!]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_owner (op : OperationPtr) (i : Nat) :
    (op.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).operands[i]!.owner =
    (op.get! ctx).operands[i]!.owner := by
  simp only [insertIntoCurrent]
  split <;> simp only [OpOperandPtr.OperationPtr_get!_setFirstUse_operands_owner,
      OpOperandPtr.OperationPtr_get!_setNextUse_operands_owner,
      OpOperandPtr.OperationPtr_get!_setBack_operands_owner]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get_insertIntoCurrent_operands_owner (op : OperationPtr) (i : Nat)
    (h : op.InBounds ctx) (hi : i < (op.get ctx h).operands.size) :
    ((op.get (OpOperandPtr.insertIntoCurrent ctx operandPtr h₁ ctxInBounds)).operands[i]'(by grind)).owner =
    ((op.get ctx).operands[i]'hi).owner := by
  have := @OpOperandPtr.OperationPtr_get!_insertIntoCurrent_operands_owner ctx ctxInBounds operandPtr h₁ op i
  grind


@[simp, grind =]
theorem OpOperandPtr.OpOperandPtr_getValue!_insertIntoCurrent (opd : OpOperandPtr)
    (operandPtr : OpOperandPtr) (hopd : opd.InBounds ctx) (operandPtrInBounds : operandPtr.InBounds ctx)
    (ctxInBounds : ctx.FieldsInBounds) :
    (opd.get! (OpOperandPtr.insertIntoCurrent ctx operandPtr operandPtrInBounds ctxInBounds)).value =
      (opd.get! ctx).value := by
  simp only [OpOperandPtr.insertIntoCurrent]
  split <;> grind

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
    split <;> grind

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
  split <;> grind

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
    (OperationPtr.get op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hop).operands.size =
    (OperationPtr.get op ctx (by grind)).operands.size := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getOperandOwner_removeFromCurrent {i : Nat} {hi} :
    ((OperationPtr.get op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hop).operands[i]'(hi)).owner =
    ((OperationPtr.get op ctx (by grind)).operands[i]'(by grind)).owner := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem OperationPtr.getBlockOperands_removeFromCurrent :
    (OperationPtr.get op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hopnd).blockOperands =
    (OperationPtr.get op ctx (by grind)).blockOperands := by
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
theorem OperationPtr.getRegions_removeFromCurrent :
    (OperationPtr.get op (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hop).regions =
    (OperationPtr.get op ctx (by grind)).regions := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getNumArguments_removeFromCurrent :
    (BlockPtr.get block (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hb).arguments.size =
    (BlockPtr.get block ctx (by grind)).arguments.size := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getArgumentOwner_removeFromCurrent {i : Nat} {hi} :
    ((BlockPtr.get block (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hb).arguments[i]'(hi)).owner =
    ((BlockPtr.get block ctx (by grind)).arguments[i]'(by grind)).owner := by
  grind [OpOperandPtr.removeFromCurrent]

@[simp, grind =]
theorem BlockPtr.getArgumentIndex_removeFromCurrent {i : Nat} {hi} :
    ((BlockPtr.get block (OpOperandPtr.removeFromCurrent ctx use h₁ h₂) hb).arguments[i]'(hi)).index =
    ((BlockPtr.get block ctx (by grind)).arguments[i]'(by grind)).index := by
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
  split <;> split <;> simp

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

end Mlir
