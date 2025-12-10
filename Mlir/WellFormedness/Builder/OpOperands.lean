-- pushOperand done
-- initOpOperands done

import Mlir.Core.Basic
import Mlir.Builder
import Mlir.WellFormedness.WellFormed
import Mlir.Lemmas.GetSet
import Mlir.Lemmas.UseDefChain

namespace Mlir

variable (ctx : IRContext)
variable (ctxInBounds : ctx.FieldsInBounds)
variable (opPtr opPtr' : OperationPtr)
variable (opPtrInBounds : opPtr.InBounds ctx := by grind)

@[simp, grind .]
theorem Builder.pushOperand_ValuePtr_InBounds_iff (valuePtr : ValuePtr) (hval : valuePtr.InBounds ctx) :
    ∀ (valuePtr' : ValuePtr), (valuePtr'.InBounds ctx) →
    (valuePtr'.InBounds (Builder.pushOperand ctx opPtr valuePtr h₁ hval h₃)) := by
  grind [Builder.pushOperand]


@[simp, grind =]
theorem Builder.pushOperand_OperandPtr_InBounds_iff (valuePtr : ValuePtr) (hval : valuePtr.InBounds ctx) :
    ∀ (operandPtr : OpOperandPtr),
    (operandPtr.InBounds (Builder.pushOperand ctx opPtr valuePtr h₁ hval h₃)) ↔ ((operandPtr.InBounds ctx) ∨ operandPtr = opPtr.nextOperand ctx) := by
  simp only [Builder.pushOperand]
  simp [←GenericPtr.iff_opOperand]
  grind

@[simp, grind =]
theorem Builder.pushOperand_ValuePtr_getFirstUse (valuePtr : ValuePtr) (hval : valuePtr.InBounds ctx)
    (valuePtr' : ValuePtr) (valuePtrInBounds' : valuePtr'.InBounds ctx) :
    valuePtr'.getFirstUse (Builder.pushOperand ctx opPtr valuePtr h₁ hval h₂) (by grind) =
    if valuePtr = valuePtr' then
      some (opPtr.nextOperand ctx)
    else
      valuePtr'.getFirstUse ctx := by
  sorry -- TODO
  -- grind [Builder.pushOperand]

theorem Builder.pushOperand_OpOperandPtr_get_firstUse (valuePtr : ValuePtr)
    valuePtrInBounds (oldFirstUse : OpOperandPtr) (hold : oldFirstUse.InBounds ctx)
    (hOldFirstUse : valuePtr.getFirstUse ctx valuePtrInBounds = some oldFirstUse) :
      oldFirstUse.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
          {oldFirstUse.get ctx (by grind) with back := OpOperandPtrPtr.operandNextUse (opPtr.nextOperand ctx)}
      := by
  simp only [←OpOperandPtr.get!_eq_get]
  simp only [Builder.pushOperand]
  sorry
  -- rw [OpOperandPtr.get!_insertIntoCurrent _ (by grind [OpOperand.FieldsInBounds]) (by grind)]
  -- · split
  --   · grind
  --   · split
  --     · grind [OpOperandPtr.InBounds, OperationPtr.get, OpOperandPtr.get]
  --     · simp; split
  --       · grind
  --       · grind
  -- · grind [OpOperandPtr.InBounds, OperationPtr.get]

include ctxInBounds in
theorem Builder.pushOperand_OpOperandPtr_get_newOperand (valuePtr : ValuePtr) valuePtrInBounds :
    (opPtr.nextOperand ctx).get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind) =
      { value := valuePtr,
        owner := opPtr,
        back := .valueFirstUse valuePtr,
        nextUse := (valuePtr.getFirstUse ctx valuePtrInBounds) } := by
  simp [Builder.pushOperand, ←OpOperandPtr.get!_eq_get]
  rw [OpOperandPtr.get!_insertIntoCurrent]
  · sorry -- grind [OpOperand.FieldsInBounds]
  · grind [OpOperand.FieldsInBounds]
  · grind [OpOperandPtr.InBounds, OperationPtr.get]
  · sorry

theorem Builder.pushOperand_OpOperandPtr_other (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (operandPtr : OpOperandPtr) (operandPtrInBounds : operandPtr.InBounds ctx)
      (_operandPtrNeFirstUse : valuePtr.getFirstUse ctx valuePtrInBounds ≠ some operandPtr),
      operandPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind) =
        operandPtr.get ctx := by
  intros operandPtr operandPtrInBounds operandPtrNeFirstUse
  simp only [←OpOperandPtr.get!_eq_get]
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent]
  -- simp only [OpOperandPtr.get_OperationPtr_setOperands, ↓reduceDIte, Array.getElem_push_eq,
  --   ValuePtr.getFirstUse_OpOperandPtr_setBack, ValuePtr.getFirstUse_OperationPtr_setOperands]
  -- split <;> simp_all <;> grind [OpOperandPtr.InBounds, OperationPtr.get, OpOperandPtr.get]
  sorry

include ctxInBounds in
@[grind =]
theorem Builder.pushOperand_OpOperandPtr_get
    (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)) :
    operandPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) operandPtrInBounds =
      if h : operandPtr = opPtr.nextOperand ctx then
        { value := valuePtr,
          owner := opPtr,
          back := OpOperandPtrPtr.valueFirstUse valuePtr,
          nextUse := (valuePtr.getFirstUse ctx valuePtrInBounds) : OpOperand}
      else if valuePtr.getFirstUse ctx (by grind) = some operandPtr then
       { operandPtr.get ctx (by grind) with back := OpOperandPtrPtr.operandNextUse (opPtr.nextOperand ctx) }
      else
        operandPtr.get ctx (by grind) := by
  grind [Builder.pushOperand_OpOperandPtr_other, Builder.pushOperand_OpOperandPtr_get_newOperand, Builder.pushOperand_OpOperandPtr_get_firstUse]

include ctxInBounds in
@[simp, grind.]
theorem Builder.pushOperand_WellFormedUseDefChain_getElem?
    (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx)
    array (arrayWf : valuePtr.WellFormedUseDefChain ctx array) (i : Nat) (hISize : i < array.size) :
    (array[i].get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind [ValuePtr.WellFormedUseDefChain])) =
      { (OpOperandPtr.get array[i] ctx (by grind [ValuePtr.WellFormedUseDefChain])) with
        back := (if i = 0 then .operandNextUse (opPtr.nextOperand ctx) else (OpOperandPtr.get array[i] ctx (by grind [ValuePtr.WellFormedUseDefChain])).back) }
    := by
  simp only
  simp (disch := grind) only [Builder.pushOperand_OpOperandPtr_get]
  split
  · grind
  · split
    · grind [ValuePtr.WellFormedUseDefChain]
    · have : i ≠ 0 := by grind [ValuePtr.WellFormedUseDefChain]
      simp [this]

set_option maxHeartbeats 10000000 in -- TODO
theorem Builder.pushOperand_WellFormedUseDefChain
    (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) (hOpWf : ctx.WellFormed)
    (valuePtr' : ValuePtr) (valuePtr'InBounds : valuePtr'.InBounds ctx) :
    ∃ array, valuePtr'.WellFormedUseDefChain (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) array (by grind) := by
  have ⟨array', arrayWf'⟩ := hOpWf.valueUseDefChains valuePtr' valuePtr'InBounds
  have ⟨array, arrayWf⟩ := hOpWf.valueUseDefChains valuePtr valuePtrInBounds
  by_cases valuePtr' = valuePtr
  -- Case where we are adding a new use
  case pos =>
    subst valuePtr'
    exists (#[opPtr.nextOperand ctx] ++ array)
    constructor
    case arrayInBounds =>
      grind [ValuePtr.WellFormedUseDefChain]
    case firstElem => grind
    case nextElems =>
      intros i hi
      simp at hi
      rw [Array.getElem?_append_right (by grind)]
      simp
      by_cases hi0 : i = 0
      · simp [hi0, Builder.pushOperand_OpOperandPtr_get_newOperand]
        grind [ValuePtr.WellFormedUseDefChain]
      · rw [@Builder.pushOperand_OpOperandPtr_get ctx (by grind) opPtr (by grind)]
        have : i = (i - 1 + 1) := by grind
        grind [ValuePtr.WellFormedUseDefChain]
    case useValue =>
      intro use hUse
      have ⟨i, hI, hUseI⟩ := Array.mem_iff_getElem.mp hUse
      grind [ValuePtr.WellFormedUseDefChain]
    case firstUseBack =>
      grind [IRContext.WellFormed]
    case prevNextUse =>
      grind (splits := 20) [ValuePtr.WellFormedUseDefChain]
    case allUsesInChain =>
      grind [ValuePtr.WellFormedUseDefChain, IRContext.WellFormed]
  -- Case where the use def chains are preserved
  case neg =>
    exists array'
    apply IRContext.ValuePtr_UseDefChainWellFormed_unchanged ctx <;>
      grind [ValuePtr.WellFormedUseDefChain]

-- /--
-- info: 'Mlir.Builder.pushOperand_WellFormedUseDefChain' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms Builder.pushOperand_WellFormedUseDefChain

theorem Builder.pushOperand_BlockOperand_get (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockOperandPtr : BlockOperandPtr) (hInBounds : blockOperandPtr.InBounds ctx) blockInBounds,
      blockOperandPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) blockInBounds = blockOperandPtr.get ctx hInBounds := by
  simp only [Builder.pushOperand, OpOperandPtr.BlockOperand_get_insertIntoCurrent]
  simp only [←BlockOperandPtr.get!_eq_get]
  grind

theorem Builder.pushOperand_BlockPtr_get_firstUse_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockPtr : BlockPtr) hBlockInBounds,
      (blockPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hBlockInBounds).firstUse =
        (blockPtr.get ctx (by grind)).firstUse := by
  grind [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_BlockPtr_get_firstUse_mono]

theorem Builder.pushOperand_BlockPtr_get_firstOp_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockPtr : BlockPtr) hBlockInBounds,
      (blockPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hBlockInBounds).firstOp =
        (blockPtr.get ctx (by grind)).firstOp := by
  grind [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_BlockPtr_get_firstOp_mono]

theorem Builder.pushOperand_BlockPtr_get_lastOp_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockPtr : BlockPtr) hBlockInBounds,
      (blockPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hBlockInBounds).lastOp =
        (blockPtr.get ctx (by grind)).lastOp := by
  grind [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_BlockPtr_get_lastOp_mono]


theorem Builder.pushOperand_OperationPtr_get_parent_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      (opPtr'.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds).parent =
        (opPtr'.get ctx (by grind)).parent := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_parent_mono]
  grind [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_parent_mono]

@[grind =]
theorem Builder.BlockPtr_get_pushOperand_parent (bl : BlockPtr) (hin : bl.InBounds ctx) :
    (bl.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).parent =
    (bl.get ctx hin).parent := by
  have := OpOperandPtr.BlockPtr_get!_insertIntoCurrent_parent
  simp only [Builder.pushOperand]
  grind

@[grind =]
theorem Builder.BlockPtr_get_pushOperand_prev (bl : BlockPtr) (hin : bl.InBounds ctx) :
    (bl.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).prev =
    (bl.get ctx hin).prev := by
  have := OpOperandPtr.BlockPtr_get!_insertIntoCurrent_prev
  simp only [Builder.pushOperand]
  grind

@[grind =]
theorem Builder.BlockPtr_get_pushOperand_next (bl : BlockPtr) (hin : bl.InBounds ctx) :
    (bl.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).next =
    (bl.get ctx hin).next := by
  have := OpOperandPtr.BlockPtr_get!_insertIntoCurrent_next
  simp only [Builder.pushOperand]
  grind

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get_pushOperand_arguments_size (bl : BlockPtr) (h : bl.InBounds ctx) valuePtr valuePtrInBounds :
    (bl.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).arguments.size =
    (bl.get ctx).arguments.size := by
  unfold Builder.pushOperand
  simp
  rw [OpOperandPtr.BlockPtr_get_insertIntoCurrent_arguments_size] <;> grind [Builder.pushOperand]

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get_pushOperand_arguments_index (bl : BlockPtr) (h : bl.InBounds ctx) valuePtr valuePtrInBounds
    (i : Nat) (hi : i < (bl.get ctx).arguments.size) :
    ((bl.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).arguments[i]'(by grind)).index =
    ((bl.get ctx).arguments[i]'hi).index := by
  grind [Builder.pushOperand]

@[simp, grind =]
theorem OpOperandPtr.BlockPtr_get_pushOperand_arguments_owner (bl : BlockPtr) (h : bl.InBounds ctx) valuePtr valuePtrInBounds
    (i : Nat) (hi : i < (bl.get ctx).arguments.size) :
    ((bl.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).arguments[i]'(by grind)).owner =
    ((bl.get ctx).arguments[i]'hi).owner := by
  grind [Builder.pushOperand]

@[grind =]
theorem Builder.RegionPtr_get_pushOperand (rg : RegionPtr) (hin : rg.InBounds ctx) :
    rg.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    rg.get ctx hin := by
  simp only [Builder.pushOperand]
  have h := OpOperandPtr.RegionPtr_get!_pushOperand
  simp only [←RegionPtr.get!_eq_get]
  grind [OperationPtr.setOperands]

theorem Builder.pushOperand_OperationPtr_get_next_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      (opPtr'.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds).next =
        (opPtr'.get ctx (by grind)).next := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_next_mono]
  grind [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_next_mono]

theorem Builder.pushOperand_OperationPtr_get_prev_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      (opPtr'.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds).prev =
        (opPtr'.get ctx (by grind)).prev := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_prev_mono]
  grind [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_prev_mono]


@[simp, grind =]
theorem Builder.pushOperand_OperationPtr_getNumRegions (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      opPtr'.getNumRegions (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds =
        opPtr'.getNumRegions ctx (by grind) := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent]
  grind

@[simp, grind =]
theorem Builder.pushOperand_OperationPtr_getRegion (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
      opPtr'.getRegion! (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
        opPtr'.getRegion! ctx := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent]
  grind

@[grind =]
theorem Builder.pushOperand_RegionPtr_get (rgPtr : RegionPtr) hRgInBounds :
      (rgPtr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hRgInBounds) =
        (rgPtr.get ctx (by grind)) := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_RegionPtr_get]
  grind [=_ RegionPtr.get!_eq_get]

@[grind =]
theorem Builder.pushOperand_OperationPtr_get_num_results (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
      opPtr'.getNumResults! (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
      opPtr'.getNumResults! ctx := by
  simp only [Builder.pushOperand, OpOperandPtr.insertIntoCurrent_OperationPtr_get_num_results]
  grind

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_Builder_pushOperand (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    opPtr'.getNumSuccessors! (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    opPtr'.getNumSuccessors! ctx := by
  grind [Builder.pushOperand]

@[simp, grind =]
theorem BlockOperandPtr.get!_Builder_pushOperand (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx)
    (blockOperandPtr : BlockOperandPtr) :
    blockOperandPtr.get! (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind [Builder.pushOperand]

@[simp, grind =]
theorem OpResultPtr.index_pushOperand :
    (OpResultPtr.get result (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) h).index =
    (OpResultPtr.get result ctx (by grind)).index := by
  grind [Builder.pushOperand]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get_pushOperand_operands_size (op : OperationPtr)
    (h : op.InBounds ctx) opPtrInBounds :
    op.getNumOperands (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    if op = opPtr then op.getNumOperands ctx + 1 else op.getNumOperands ctx := by
  simp only [Builder.pushOperand]
  grind

@[grind =]
theorem OpOperandPtr.OperationPtr_get_pushOperand_operands_owner {opr : OpOperandPtr} {h} :
    (opr.get (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) h).owner =
    if h: opr = opPtr.nextOperand ctx then
      opPtr
    else
      (opr.get ctx).owner := by
  simp only [Builder.pushOperand, owner_insertIntoCurrent]
  simp only [←OpOperandPtr.get!_eq_get]
  grind

theorem Builder.pushOperand_WellFormed  (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) (hOpWf : ctx.WellFormed) :
    (Builder.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds).WellFormed := by
  constructor
  case valueUseDefChains =>
    grind [Builder.pushOperand_WellFormedUseDefChain]
  case blockUseDefChains =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.blockUseDefChains blockPtr (by grind)
    exists array
    apply IRContext.BlockPtr_UseDefChainWellFormed_unchanged ctx
    · grind [IRContext.WellFormed]
    · grind [Builder.pushOperand_BlockPtr_get_firstUse_mono]
    · grind [Builder.pushOperand_BlockOperand_get]
    · grind [Builder.pushOperand_BlockOperand_get]
    · grind
    · grind
  case inBounds => grind
  case opChain =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.opChain blockPtr (by grind)
    exists array
    apply IRContext.OperationChainWellFormed_unchanged ctx <;>
      grind [pushOperand_OperationPtr_get_parent_mono, pushOperand_OperationPtr_get_prev_mono,
        pushOperand_OperationPtr_get_next_mono, pushOperand_BlockPtr_get_lastOp_mono, pushOperand_BlockPtr_get_firstOp_mono]
  case blockChain =>
    intros reg hreg
    have ⟨array, arrayWf⟩ := hOpWf.blockChain reg (by grind)
    exists array
    apply @IRContext.BlockChainWellFormed_unchanged (ctx := ctx) <;>
      grind [pushOperand_OperationPtr_get_parent_mono, pushOperand_OperationPtr_get_prev_mono,
        pushOperand_OperationPtr_get_next_mono, pushOperand_BlockPtr_get_lastOp_mono, pushOperand_BlockPtr_get_firstOp_mono]
  case operations =>
    intros opPtr' opPtrInBounds
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hOpWf.operations opPtr' (by grind)
    constructor <;> try grind [Builder.pushOperand, Operation.WellFormed, OperationPtr.getOpOperand]
  case blocks =>
    intros bl hbl
    constructor
    · grind
    · intros i hi
      have ⟨h₁, h₂, h₃⟩ := hOpWf.blocks bl (by grind)
      grind
    · intros i hi
      have ⟨h₁, h₂, h₃⟩ := hOpWf.blocks bl (by grind)
      grind
  case regions =>
    intros reg hreg
    have ⟨h₁, h₂⟩ := hOpWf.regions reg (by grind)
    constructor
    · grind [Builder.pushOperand]
    · grind

-- /--
-- info: 'Mlir.Builder.pushOperand_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms Builder.pushOperand_WellFormed

theorem Builder.initOpOperands_WellFormed (ctx: IRContext) (opPtr: OperationPtr) (opPtrInBounds : opPtr.InBounds ctx)
    (operands : Array ValuePtr) (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx) (hctx : ctx.FieldsInBounds)
    (n : Nat := operands.size) (hn : 0 ≤ n ∧ n ≤ operands.size := by grind)
    (hOpWf : ctx.WellFormed) :
    (Builder.initOpOperands ctx opPtr opPtrInBounds operands hoperands hctx n hn).WellFormed := by
  induction n generalizing ctx
  case zero =>
    grind [initOpOperands]
  case succ n ih =>
    simp only [initOpOperands]
    grind [Builder.pushOperand_WellFormed]
