import Mlir.Core.Basic
import Mlir.Core.WellFormed
import Mlir.Rewriter.Basic
import Mlir.Rewriter.GetSetInBounds
import Mlir.Rewriter.LinkedList.GetSet

namespace Mlir

variable (ctx : IRContext)
variable (ctxInBounds : ctx.FieldsInBounds)
variable (opPtr opPtr' : OperationPtr)
variable (opPtrInBounds : opPtr.InBounds ctx := by grind)

@[simp, grind .]
theorem Rewriter.pushOperand_ValuePtr_InBounds_iff (valuePtr : ValuePtr) (hval : valuePtr.InBounds ctx) :
    ∀ (valuePtr' : ValuePtr), (valuePtr'.InBounds ctx) →
    (valuePtr'.InBounds (Rewriter.pushOperand ctx opPtr valuePtr h₁ hval h₃)) := by
  grind [Rewriter.pushOperand]


@[simp, grind =]
theorem Rewriter.pushOperand_OperandPtr_InBounds_iff (valuePtr : ValuePtr) (hval : valuePtr.InBounds ctx) :
    ∀ (operandPtr : OpOperandPtr),
    (operandPtr.InBounds (Rewriter.pushOperand ctx opPtr valuePtr h₁ hval h₃)) ↔ ((operandPtr.InBounds ctx) ∨ operandPtr = opPtr.nextOperand ctx) := by
  simp only [Rewriter.pushOperand]
  simp [←GenericPtr.iff_opOperand]
  grind

@[simp, grind =]
theorem Rewriter.pushOperand_ValuePtr_getFirstUse (valuePtr : ValuePtr) (hval : valuePtr.InBounds ctx)
    (valuePtr' : ValuePtr) (valuePtrInBounds' : valuePtr'.InBounds ctx) :
    valuePtr'.getFirstUse (Rewriter.pushOperand ctx opPtr valuePtr h₁ hval h₂) (by grind) =
    if valuePtr = valuePtr' then
      some (opPtr.nextOperand ctx)
    else
      valuePtr'.getFirstUse ctx := by
  sorry -- TODO
  -- grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_OpOperandPtr_get_firstUse (valuePtr : ValuePtr)
    valuePtrInBounds (oldFirstUse : OpOperandPtr) (hold : oldFirstUse.InBounds ctx)
    (hOldFirstUse : valuePtr.getFirstUse ctx valuePtrInBounds = some oldFirstUse) :
      oldFirstUse.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
          {oldFirstUse.get ctx (by grind) with back := OpOperandPtrPtr.operandNextUse (opPtr.nextOperand ctx)}
      := by
  simp only [←OpOperandPtr.get!_eq_get]
  simp only [Rewriter.pushOperand]
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
theorem Rewriter.pushOperand_OpOperandPtr_get_newOperand (valuePtr : ValuePtr) valuePtrInBounds :
    (opPtr.nextOperand ctx).get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind) =
      { value := valuePtr,
        owner := opPtr,
        back := .valueFirstUse valuePtr,
        nextUse := (valuePtr.getFirstUse ctx valuePtrInBounds) } := by
  simp [Rewriter.pushOperand, ←OpOperandPtr.get!_eq_get]
  grind

theorem Rewriter.pushOperand_OpOperandPtr_other (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (operandPtr : OpOperandPtr) (operandPtrInBounds : operandPtr.InBounds ctx)
      (_operandPtrNeFirstUse : valuePtr.getFirstUse ctx valuePtrInBounds ≠ some operandPtr),
      operandPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind) =
        operandPtr.get ctx := by
  intros operandPtr operandPtrInBounds operandPtrNeFirstUse
  simp only [←OpOperandPtr.get!_eq_get]
  simp only [Rewriter.pushOperand, OpOperandPtr.insertIntoCurrent]
  -- simp only [OpOperandPtr.get_OperationPtr_setOperands, ↓reduceDIte, Array.getElem_push_eq,
  --   ValuePtr.getFirstUse_OpOperandPtr_setBack, ValuePtr.getFirstUse_OperationPtr_setOperands]
  -- split <;> simp_all <;> grind [OpOperandPtr.InBounds, OperationPtr.get, OpOperandPtr.get]
  sorry

include ctxInBounds in
@[grind =]
theorem Rewriter.pushOperand_OpOperandPtr_get
    (valuePtr : ValuePtr) valuePtrInBounds (operandPtr : OpOperandPtr)
    (operandPtrInBounds : operandPtr.InBounds (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)) :
    operandPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) operandPtrInBounds =
      if h : operandPtr = opPtr.nextOperand ctx then
        { value := valuePtr,
          owner := opPtr,
          back := OpOperandPtrPtr.valueFirstUse valuePtr,
          nextUse := (valuePtr.getFirstUse ctx valuePtrInBounds) : OpOperand}
      else if valuePtr.getFirstUse ctx (by grind) = some operandPtr then
       { operandPtr.get ctx (by grind) with back := OpOperandPtrPtr.operandNextUse (opPtr.nextOperand ctx) }
      else
        operandPtr.get ctx (by grind) := by
  grind [Rewriter.pushOperand_OpOperandPtr_other, Rewriter.pushOperand_OpOperandPtr_get_newOperand, Rewriter.pushOperand_OpOperandPtr_get_firstUse]

include ctxInBounds in
@[simp, grind.]
theorem Rewriter.pushOperand_WellFormedUseDefChain_getElem?
    (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx)
    array (arrayWf : valuePtr.WellFormedUseDefChain ctx array) (i : Nat) (hISize : i < array.size) :
    (array[i].get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) (by grind [ValuePtr.WellFormedUseDefChain])) =
      { (OpOperandPtr.get array[i] ctx (by grind [ValuePtr.WellFormedUseDefChain])) with
        back := (if i = 0 then .operandNextUse (opPtr.nextOperand ctx) else (OpOperandPtr.get array[i] ctx (by grind [ValuePtr.WellFormedUseDefChain])).back) }
    := by
  simp only
  simp (disch := grind) only [Rewriter.pushOperand_OpOperandPtr_get]
  split
  · grind
  · split
    · grind [ValuePtr.WellFormedUseDefChain]
    · have : i ≠ 0 := by grind [ValuePtr.WellFormedUseDefChain]
      simp [this]

set_option maxHeartbeats 10000000 in -- TODO
theorem Rewriter.pushOperand_WellFormedUseDefChain
    (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) (hOpWf : ctx.WellFormed)
    (valuePtr' : ValuePtr) (valuePtr'InBounds : valuePtr'.InBounds ctx) :
    ∃ array, valuePtr'.WellFormedUseDefChain (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) array (by grind) := by
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
      by_cases hi0 : i = 0 <;> grind [ValuePtr.WellFormedUseDefChain]
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
    apply IRContext.ValuePtr_UseDefChainWellFormed_unchanged (ctx := ctx) <;>
      grind [ValuePtr.WellFormedUseDefChain]

-- /--
-- info: 'Mlir.Rewriter.pushOperand_WellFormedUseDefChain' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms Rewriter.pushOperand_WellFormedUseDefChain

theorem Rewriter.pushOperand_BlockOperand_get (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockOperandPtr : BlockOperandPtr) (hInBounds : blockOperandPtr.InBounds ctx) blockInBounds,
      blockOperandPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) blockInBounds = blockOperandPtr.get ctx hInBounds := by
  simp only [Rewriter.pushOperand]
  grind

theorem Rewriter.pushOperand_BlockPtr_get_firstUse_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockPtr : BlockPtr) hBlockInBounds,
      (blockPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hBlockInBounds).firstUse =
        (blockPtr.get ctx (by grind)).firstUse := by
  grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_BlockPtr_get_firstOp_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockPtr : BlockPtr) hBlockInBounds,
      (blockPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hBlockInBounds).firstOp =
        (blockPtr.get ctx (by grind)).firstOp := by
  grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_BlockPtr_get_lastOp_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    ∀ (blockPtr : BlockPtr) hBlockInBounds,
      (blockPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hBlockInBounds).lastOp =
        (blockPtr.get ctx (by grind)).lastOp := by
  grind [Rewriter.pushOperand]


theorem Rewriter.pushOperand_OperationPtr_get_parent_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      (opPtr'.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds).parent =
        (opPtr'.get ctx (by grind)).parent := by
  grind [Rewriter.pushOperand]

@[grind =]
theorem Rewriter.BlockPtr_get_pushOperand_parent (bl : BlockPtr) (hin : bl.InBounds ctx) :
    (bl.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).parent =
    (bl.get ctx hin).parent := by
  grind [Rewriter.pushOperand]

@[grind =]
theorem Rewriter.BlockPtr_get_pushOperand_prev (bl : BlockPtr) (hin : bl.InBounds ctx) :
    (bl.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).prev =
    (bl.get ctx hin).prev := by
  grind [Rewriter.pushOperand]

@[grind =]
theorem Rewriter.BlockPtr_get_pushOperand_next (bl : BlockPtr) (hin : bl.InBounds ctx) :
    (bl.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).next =
    (bl.get ctx hin).next := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem BlockPtr.getNumArguments!_Rewriter_pushOperand :
    BlockPtr.getNumArguments! block (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    BlockPtr.getNumArguments! block ctx := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem BlockArgumentPtr.index!_Rewriter_pushOperand :
    (BlockArgumentPtr.get! arg (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).index =
    (BlockArgumentPtr.get! arg ctx).index := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem BlockArgumentPtr.owner!_Rewriter_pushOperand :
    (BlockArgumentPtr.get! arg (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds)).owner =
    (BlockArgumentPtr.get! arg ctx).owner := by
  grind [Rewriter.pushOperand]

@[grind =]
theorem Rewriter.RegionPtr_get_pushOperand (rg : RegionPtr) (hin : rg.InBounds ctx) :
    rg.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    rg.get ctx hin := by
  grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_OperationPtr_get_next_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      (opPtr'.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds).next =
        (opPtr'.get ctx (by grind)).next := by
  grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_OperationPtr_get_prev_mono (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      (opPtr'.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds).prev =
        (opPtr'.get ctx (by grind)).prev := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem Rewriter.pushOperand_OperationPtr_getNumRegions (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) hOp'InBounds :
      opPtr'.getNumRegions (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hOp'InBounds =
        opPtr'.getNumRegions ctx (by grind) := by
  simp only [Rewriter.pushOperand, OpOperandPtr.insertIntoCurrent]
  grind

@[simp, grind =]
theorem Rewriter.pushOperand_OperationPtr_getRegion (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
      opPtr'.getRegion! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
        opPtr'.getRegion! ctx := by
  simp only [Rewriter.pushOperand, OpOperandPtr.insertIntoCurrent]
  grind

@[grind =]
theorem Rewriter.pushOperand_RegionPtr_get (rgPtr : RegionPtr) hRgInBounds :
      (rgPtr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) hRgInBounds) =
        (rgPtr.get ctx (by grind)) := by
  grind [Rewriter.pushOperand]

@[grind =]
theorem Rewriter.pushOperand_OperationPtr_get_num_results (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
      opPtr'.getNumResults! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
      opPtr'.getNumResults! ctx := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem OperationPtr.getNumSuccessors!_Rewriter_pushOperand (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) :
    opPtr'.getNumSuccessors! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    opPtr'.getNumSuccessors! ctx := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem BlockOperandPtr.get!_Rewriter_pushOperand (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx)
    (blockOperandPtr : BlockOperandPtr) :
    blockOperandPtr.get! (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    blockOperandPtr.get! ctx := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem OpResultPtr.index_pushOperand :
    (OpResultPtr.get result (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) h).index =
    (OpResultPtr.get result ctx (by grind)).index := by
  grind [Rewriter.pushOperand]

@[simp, grind =]
theorem OpOperandPtr.OperationPtr_get_pushOperand_operands_size (op : OperationPtr)
    (h : op.InBounds ctx) opPtrInBounds :
    op.getNumOperands (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) =
    if op = opPtr then op.getNumOperands ctx + 1 else op.getNumOperands ctx := by
  simp only [Rewriter.pushOperand]
  grind

@[grind =]
theorem OpOperandPtr.OperationPtr_get_pushOperand_operands_owner {opr : OpOperandPtr} {h} :
    (opr.get (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds) h).owner =
    if h: opr = opPtr.nextOperand ctx then
      opPtr
    else
      (opr.get ctx).owner := by
  grind [Rewriter.pushOperand]

theorem Rewriter.pushOperand_WellFormed  (valuePtr : ValuePtr) (valuePtrInBounds : valuePtr.InBounds ctx) (hOpWf : ctx.WellFormed) :
    (Rewriter.pushOperand ctx opPtr valuePtr opPtrInBounds valuePtrInBounds ctxInBounds).WellFormed := by
  constructor
  case valueUseDefChains =>
    grind [Rewriter.pushOperand_WellFormedUseDefChain]
  case blockUseDefChains =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.blockUseDefChains blockPtr (by grind)
    exists array
    apply IRContext.BlockPtr_UseDefChainWellFormed_unchanged (ctx := ctx)
    · grind [IRContext.WellFormed]
    · grind [Rewriter.pushOperand_BlockOperand_get]
    · grind [Rewriter.pushOperand_BlockPtr_get_firstUse_mono]
    · grind [Rewriter.pushOperand_BlockOperand_get]
    · grind
    · grind
  case inBounds => grind
  case opChain =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := hOpWf.opChain blockPtr (by grind)
    exists array
    apply IRContext.OperationChainWellFormed_unchanged (ctx := ctx) <;>
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
    constructor
    case region_parent =>
      intros region regionInBounds
      simp only [pushOperand_OperationPtr_getRegion]
      grind
    all_goals grind [Rewriter.pushOperand, Operation.WellFormed, OperationPtr.getOpOperand]
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
    · grind [Rewriter.pushOperand]
    · grind

-- /--
-- info: 'Mlir.Rewriter.pushOperand_WellFormed' depends on axioms: [propext, Classical.choice, Quot.sound]
-- -/
-- #guard_msgs in
-- #print axioms Rewriter.pushOperand_WellFormed

theorem Rewriter.initOpOperands_WellFormed (ctx: IRContext) (opPtr: OperationPtr) (opPtrInBounds : opPtr.InBounds ctx)
    (operands : Array ValuePtr) (hoperands : ∀ oper, oper ∈ operands → oper.InBounds ctx) (hctx : ctx.FieldsInBounds)
    (n : Nat := operands.size) (hn : 0 ≤ n ∧ n ≤ operands.size := by grind)
    (hOpWf : ctx.WellFormed) :
    (Rewriter.initOpOperands ctx opPtr opPtrInBounds operands hoperands hctx n hn).WellFormed := by
  induction n generalizing ctx
  case zero =>
    grind [initOpOperands]
  case succ n ih =>
    simp only [initOpOperands]
    grind [Rewriter.pushOperand_WellFormed]
