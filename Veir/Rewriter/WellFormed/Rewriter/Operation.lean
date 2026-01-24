import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds
import Veir.Rewriter.InsertPoint

namespace Veir

section insertOp

theorem Rewriter.insertOp?_WellFormed (ctx : IRContext) (hctx : ctx.WellFormed)
    (newOp : OperationPtr) (ip : InsertPoint)
    (newOpIn : newOp.InBounds ctx := by grind)
    (insIn : ip.InBounds ctx)
    (hwf : ip.block! ctx = some block)
    (ctxInBounds : ctx.FieldsInBounds) (newCtx : IRContext) :
    Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some newCtx →
    newCtx.WellFormed := by
  intros heq
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx
  constructor
  case inBounds =>
    grind
  case valueDefUseChains =>
    intros val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  case opChain =>
    intros block' hblock'
    have ⟨array, harray⟩ := h₄ block (by grind)
    have ⟨array', harray⟩ := h₄ block' (by grind)
    have hNewCtx : newOp.linkBetweenWithParent ctx (ip.prev! ctx) ip.next block (by grind) (by grind) (by grind) (by grind) = some newCtx := by grind [insertOp?]
    simp only [insertOp?] at heq
    by_cases block = block'
    · subst block'
      apply Exists.intro _
      apply BlockPtr.opChain_OperationPtr_linkBetweenWithParent_self (ctx := ctx) (by grind)
        hNewCtx (ip := ip) (by grind) (by grind) (by grind) (by grind) harray
    · exists array'
      apply BlockPtr.opChain_OperationPtr_linkBetweenWithParent_other (ctx := ctx) hNewCtx <;>
        grind [InsertPoint.prev.maybe₁_parent, InsertPoint.next.maybe₁_parent]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    simp [insertOp?] at heq
    split at heq; grind
    intro op opInBounds
    apply Operation.wellFormed_OperationPtr_linkBetweenWithParent ctxInBounds (hctx := heq)
    · grind [InsertPoint.prev.maybe₁_parent]
    · grind [InsertPoint.next.maybe₁_parent]
    · grind
    · grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    grind [Block.WellFormed_unchanged]
  case regions =>
    grind [Region.WellFormed_unchanged]

end insertOp

section detachOp

theorem BlockPtr.opChain_detachOp_other
    (hWf : BlockPtr.OpChain block ctx array)
    (hWf' : BlockPtr.OpChain block' ctx array') :
    (op.get! ctx).parent = some block' →
    block ≠ block' →
    BlockPtr.OpChain block (Rewriter.detachOp ctx op hctx hIn hasParent) array := by
  intro hParent hNe
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

set_option maxHeartbeats 400000 in
theorem BlockPtr.opChain_detachOp_self
    (hWf : BlockPtr.OpChain block ctx array) :
    (op.get! ctx).parent = some block →
    BlockPtr.OpChain block (Rewriter.detachOp ctx op hctx hIn hasParent) (array.erase op) := by
  intro hParent
  have opInArray : op ∈ array := by grind [OpChain]
  have ⟨i, iInBounds, hi⟩ := Array.getElem_of_mem opInArray
  constructor
  case prev =>
    subst op
    intros i' hi₁' hi₂'
    simp only [BlockPtr.OpChain.erase_getElem_array_eq_eraseIdx hWf]
    by_cases i' < i
    · simp (disch := grind) only [Array.getElem_eraseIdx_of_lt]
      simp only [OperationPtr.prev!_detachOp]
      grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases i' = i
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
  case next =>
    subst op
    intros i' hi'
    simp only [BlockPtr.OpChain.erase_getElem_array_eq_eraseIdx hWf]
    by_cases i' > i
    · simp (disch := grind) only [Array.getElem_eraseIdx_of_ge, Array.getElem?_eraseIdx_of_ge]
      simp only [OperationPtr.next!_detachOp]
      grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
    · by_cases i' = i
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
      · grind [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
  all_goals grind [OpChain]

theorem ValuePtr.defUse_detachOp
    (hWf : ValuePtr.DefUse value ctx array missingUses) :
    ValuePtr.DefUse value (Rewriter.detachOp ctx op hctx hIn hasParent) array missingUses := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem BlockPtr.defUse_detachOp
    (hWf : BlockPtr.DefUse block ctx array missingUses) :
    BlockPtr.DefUse block (Rewriter.detachOp ctx op hctx hIn hasParent) array missingUses := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind

theorem RegionPtr.blockChain_detachOp
    (hWf : RegionPtr.BlockChain region ctx array) :
    RegionPtr.BlockChain region (Rewriter.detachOp ctx op hctx hIn hasParent) array := by
  apply RegionPtr.blockChain_unchanged (ctx := ctx) hWf <;> grind

theorem Rewriter.detachOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hIn : op.InBounds ctx)
    (hasParent : (op.get ctx hIn).parent.isSome) :
    (Rewriter.detachOp ctx op hctx hIn hasParent).WellFormed := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf
  constructor
  case inBounds => grind
  case valueDefUseChains =>
    intros val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    grind [ValuePtr.defUse_detachOp]
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    grind [BlockPtr.defUse_detachOp]
  case opChain =>
    intros block' hBlock'
    have ⟨array', harray'⟩ := h₄ block' (by grind)
    have ⟨block, hBlock⟩ := Option.isSome_iff_exists.mp hasParent
    by_cases hEq : block = block'
    · exists array'.erase op
      grind [BlockPtr.opChain_detachOp_self]
    · exists array'
      have ⟨array, harray⟩ := h₄ block (by grind)
      grind [BlockPtr.opChain_detachOp_other]
  case blockChain =>
    intros region hregion
    have ⟨array, harray⟩ := h₅ region (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    intros op' hop'
    have : op'.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := h₆ op' this
    constructor
    case region_parent =>
      -- TODO: why does grind does not work here and require this simp?
      simp; grind
    case opChain_of_parent_none =>
      cases hParent: (op.get! ctx).parent
        <;> grind [BlockPtr.OpChain_next_ne, BlockPtr.OpChain_prev_ne]
    all_goals grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    grind [Block.WellFormed_unchanged]
  case regions =>
    grind [Region.WellFormed_unchanged]

end detachOp

section detachOpIfAttached

theorem BlockPtr.opChain_detachOpIfAttached_other
    (hWf : BlockPtr.OpChain block ctx array)
    (hWf' : BlockPtr.OpChain block' ctx array') :
    (op.get! ctx).parent = some block' →
    block ≠ block' →
    BlockPtr.OpChain block (Rewriter.detachOpIfAttached ctx op hctx hIn) array := by
  simp only [Rewriter.detachOpIfAttached]
  grind [BlockPtr.opChain_detachOp_other]

theorem BlockPtr.opChain_detachOpIfAttached_self
    (hWf : BlockPtr.OpChain block ctx array) :
    (op.get! ctx).parent = some block →
    BlockPtr.OpChain block (Rewriter.detachOpIfAttached ctx op hctx hIn) (array.erase op) := by
  simp only [Rewriter.detachOpIfAttached]
  grind [BlockPtr.opChain_detachOp_self]

theorem BlockPtr.opChain_detachOpIfAttached_none
    (hWf : BlockPtr.OpChain block ctx array) :
    (op.get! ctx).parent = none →
    BlockPtr.OpChain block (Rewriter.detachOpIfAttached ctx op hctx hIn) array := by
  simp only [Rewriter.detachOpIfAttached]
  grind

theorem ValuePtr.defUse_detachOpIfAttached
    (hWf : ValuePtr.DefUse value ctx array missingUses) :
    ValuePtr.DefUse value (Rewriter.detachOpIfAttached ctx op hctx hIn) array missingUses := by
  simp only [Rewriter.detachOpIfAttached]
  grind [ValuePtr.defUse_detachOp]

theorem BlockPtr.defUse_detachOpIfAttached
    (hWf : BlockPtr.DefUse block ctx array missingUses) :
    BlockPtr.DefUse block (Rewriter.detachOpIfAttached ctx op hctx hIn) array missingUses := by
  simp only [Rewriter.detachOpIfAttached]
  grind [BlockPtr.defUse_detachOp]

theorem RegionPtr.blockChain_detachOpIfAttached
    (hWf : RegionPtr.BlockChain region ctx array) :
    RegionPtr.BlockChain region (Rewriter.detachOpIfAttached ctx op hctx hIn) array := by
  simp only [Rewriter.detachOpIfAttached]
  grind [RegionPtr.blockChain_detachOp]

theorem Rewriter.detachOpIfAttached_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hIn : op.InBounds ctx) :
    (Rewriter.detachOpIfAttached ctx op hctx hIn).WellFormed := by
  simp only [Rewriter.detachOpIfAttached]
  grind [Rewriter.detachOp_WellFormed]

end detachOpIfAttached

theorem Rewriter.detachOperands.loop_wellFormed
    (wf : IRContext.WellFormed ctx missingOperands missingSuccessors)
    (hMissingOperands : ∀ i, i <= index → (OpOperandPtr.mk op i) ∉ missingOperands) :
    (Rewriter.detachOperands.loop ctx op index hCtx hOp hIndex).WellFormed
      (missingOperands.insertMany ((0...=index).toList.map (fun i => OpOperandPtr.mk op i)))
      missingSuccessors := by
  induction index generalizing ctx missingOperands missingSuccessors
  case zero =>
    simp only [loop, Nat.toList_rcc_eq_singleton, List.map_cons, List.map_nil,
      Std.ExtHashSet.insertMany_list_singleton]
    grind [IRContext.wellFormed_OpOperandPtr_removeFromCurrent]
  case succ index hi =>
    simp only [loop, Nat.succ_eq_add_one, Nat.le_add_left, Nat.toList_rcc_eq_append,
      List.map_append, List.map_cons, List.map_nil, Std.ExtHashSet.insertMany_append,
      Std.ExtHashSet.insertMany_list_singleton]
    have h := @hi (OpOperandPtr.removeFromCurrent ctx {op := op, index := index + 1})
      (missingOperands.insert (OpOperandPtr.mk op (index + 1))) missingSuccessors (by grind)
      (by grind) (by grind) (by grind [IRContext.wellFormed_OpOperandPtr_removeFromCurrent]) (by grind)
    grind [Std.ExtHashSet.insertMany_list_insert_comm, Nat.toList_rcc_eq_toList_rco]

theorem Rewriter.detachOperands_wellFormed
    (wf : IRContext.WellFormed ctx missingOperands missingSuccessors)
    (hMissingOperands : ∀ i, (OpOperandPtr.mk op i) ∉ missingOperands) :
    (Rewriter.detachOperands ctx op hCtx hOp).WellFormed
      (missingOperands.insertMany ((0...op.getNumOperands! ctx).toList.map (fun i => OpOperandPtr.mk op i)))
      missingSuccessors := by
  simp only [Rewriter.detachOperands]
  split
  case isTrue h =>
    rw [← OperationPtr.getNumOperands!_eq_getNumOperands (hin := by grind)] at h
    simp [h]
    grind
  case isFalse h=>
    have := @Rewriter.detachOperands.loop_wellFormed ctx missingOperands missingSuccessors
      (op.getNumOperands ctx - 1) op hCtx hOp (by grind) wf (by grind)
    grind [Nat.toList_rcc_eq_toList_rco]

theorem Rewriter.detachBlockOperands.loop_wellFormed
    (wf : IRContext.WellFormed ctx missingOperands missingSuccessors)
    (hMissingSuccessors : ∀ i, i <= index → (BlockOperandPtr.mk op i) ∉ missingSuccessors) :
    (Rewriter.detachBlockOperands.loop ctx op index hCtx hOp hIndex).WellFormed
      missingOperands
      (missingSuccessors.insertMany ((0...=index).toList.map (fun i => BlockOperandPtr.mk op i)))
       := by
  induction index generalizing ctx missingOperands missingSuccessors
  case zero =>
    simp only [loop, Nat.toList_rcc_eq_singleton, List.map_cons, List.map_nil,
      Std.ExtHashSet.insertMany_list_singleton]
    grind [IRContext.wellFormed_BlockOperandPtr_removeFromCurrent]
  case succ index hi =>
    simp only [loop, Nat.succ_eq_add_one, Nat.le_add_left, Nat.toList_rcc_eq_append,
      List.map_append, List.map_cons, List.map_nil, Std.ExtHashSet.insertMany_append,
      Std.ExtHashSet.insertMany_list_singleton]
    have h := @hi (BlockOperandPtr.removeFromCurrent ctx {op := op, index := index + 1})
      missingOperands (missingSuccessors.insert (BlockOperandPtr.mk op (index + 1))) (by grind)
      (by grind) (by grind) (by grind [IRContext.wellFormed_BlockOperandPtr_removeFromCurrent]) (by grind)
    grind [Std.ExtHashSet.insertMany_list_insert_comm, Nat.toList_rcc_eq_toList_rco]

theorem Rewriter.detachBlockOperands_wellFormed
    (wf : IRContext.WellFormed ctx missingOperands missingSuccessors)
    (hMissingSuccessors : ∀ i, (BlockOperandPtr.mk op i) ∉ missingSuccessors) :
    (Rewriter.detachBlockOperands ctx op hCtx hOp).WellFormed missingOperands
      (missingSuccessors.insertMany
        ((0...op.getNumSuccessors! ctx).toList.map (fun i => BlockOperandPtr.mk op i))) := by
  simp only [Rewriter.detachBlockOperands]
  split
  case isTrue h =>
    rw [← OperationPtr.getNumSuccessors!_eq_getNumSuccessors (hin := by grind)] at h
    simp [h]
    grind
  case isFalse h=>
    have := @Rewriter.detachBlockOperands.loop_wellFormed ctx missingOperands missingSuccessors
      (op.getNumSuccessors ctx - 1) op hCtx hOp (by grind) wf (by grind)
    grind [Nat.toList_rcc_eq_toList_rco]

set_option warn.sorry false in
theorem Rewriter.eraseOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hop : op.InBounds ctx)
    (newCtx : IRContext) :
    Rewriter.eraseOp ctx op hctx hop = newCtx →
    newCtx.WellFormed := by
  sorry

set_option warn.sorry false in
theorem BlockPtr.operationList_Rewriter_eraseOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.eraseOp ctx op hctx hop) ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

set_option warn.sorry false in
theorem OperationPtr.getOperand_Rewriter_eraseOp
    (heq : Rewriter.eraseOp ctx op hctx hop = newCtx) (hne : op ≠ op'):
    OperationPtr.getOperand op' newCtx idx inBounds idxInBounds =
    OperationPtr.getOperand op' ctx idx (by sorry) (by sorry) := by
  sorry

end Veir
