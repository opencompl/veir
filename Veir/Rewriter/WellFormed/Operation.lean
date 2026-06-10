module

public import Veir.IR.Basic
public import Veir.Rewriter.Basic

import all Veir.Rewriter.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSet
import Veir.Rewriter.LinkedList.GetSet
import Veir.Rewriter.WellFormed.BlockOperands
import Veir.Rewriter.WellFormed.OpOperands
import Veir.Rewriter.WellFormed.OpRegion
import Veir.Rewriter.WellFormed.OpResults
import Veir.IR.DeallocLemmas

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

section insertOp

theorem Rewriter.insertOp?_WellFormed (hctx : ctx.WellFormed) :
    Rewriter.insertOp? ctx newOp ip newOpIn insIn ctxInBounds = some newCtx →
    newCtx.WellFormed := by
  simp only [Rewriter.insertOp?]
  split; grind; rename_i parent hparent
  intro h
  apply IRContext.wellFormed_OperationPtr_linkBetweenWithParent hctx h (ip := ip) <;>
    grind [Option.maybe₁_def]

theorem BlockPtr.operationList_rewriter_insertOp?
  (h : Rewriter.insertOp? ctx op ip opIn ipIn ctxIn = some ctx') (ctxWf : ctx.WellFormed) :
  BlockPtr.operationList block ctx' ctx'Wf blockIn =
  if h: ip.block! ctx = some block then
    (BlockPtr.operationList block ctx ctxWf).insertIdx (ip.idxIn ctx block) op
      (by apply InsertPoint.idxIn.le_size_operationList)
  else
    BlockPtr.operationList block ctx ctxWf := by
  have ⟨block', hBlock'⟩ : ∃ block', ip.block! ctx = some block' := by grind [Rewriter.insertOp?]
  have ⟨array, hArray⟩ := ctxWf.opChain block (by grind)
  have ⟨array', hArray'⟩ := ctxWf.opChain block' (by grind)
  simp only [Rewriter.insertOp?] at h
  split at h; grind; rename_i parent hparent
  have : block' = parent := by grind
  subst parent
  by_cases heq : block = block'
  · subst block'
    simp only [hBlock', ↓reduceDIte]
    have := BlockPtr.opChain_OperationPtr_linkBetweenWithParent_self (ctx := ctx) (by grind)
      h (ip := ip) (by grind) (by grind) (by grind) (by grind) hArray
    simp [BlockPtr.operationList_iff_BlockPtr_OpChain.mp this,
          BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
  · have h := BlockPtr.opChain_OperationPtr_linkBetweenWithParent_other (ctx := ctx) h (array := array) (block' := block)
    simp only [← InsertPoint.prev!_eq_prev] at h
    have h := h (by grind [InsertPoint.prev.maybe₁_parent_of_opChain])
    have h := h (by grind [InsertPoint.next.maybe₁_parent_of_opChain])
    have h := h (by grind) (by grind)
    grind [BlockPtr.operationList_iff_BlockPtr_OpChain.mp h,
          BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]

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
      grind (instances := 2000) [BlockPtr.OpChain, BlockPtr.OpChain_array_injective]
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

theorem Rewriter.detachOp_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
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
      intro region regionInBounds
      apply OperationPtr.WellFormed.region_parent.unchanged (ctx := ctx) <;> grind
    case opChain_of_parent_none =>
      cases hParent: (op.get! ctx).parent
        <;> grind [BlockPtr.OpChain_next_ne, BlockPtr.OpChain_prev_ne]
    all_goals grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    grind [BlockPtr.WellFormed_unchanged]
  case regions =>
    grind [RegionPtr.WellFormed_unchanged]

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

theorem Rewriter.detachOpIfAttached_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hIn : op.InBounds ctx) :
    (Rewriter.detachOpIfAttached ctx op hctx hIn).WellFormed := by
  simp only [Rewriter.detachOpIfAttached]
  grind [Rewriter.detachOp_WellFormed]

theorem BlockPtr.operationList_rewriter_detachOpIfAttached (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block (Rewriter.detachOpIfAttached ctx op hctx hIn)
      (by grind [Rewriter.detachOpIfAttached_WellFormed]) (by grind) =
    if (op.get! ctx).parent = block then
      (BlockPtr.operationList block ctx ctxWf blockIn).erase op
    else
      BlockPtr.operationList block ctx ctxWf blockIn := by
  have ⟨array, hArray⟩ := ctxWf.opChain block (by grind)
  cases hparent : (op.get! ctx).parent with
  | none =>
    simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp
        (BlockPtr.opChain_detachOpIfAttached_none hArray hparent),
      BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
    grind
  | some block' =>
    by_cases heq : block' = block
    · subst block'
      simp only [↓reduceIte]
      simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp
        (BlockPtr.opChain_detachOpIfAttached_self hArray hparent)]
      simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]
    · simp only [Option.some.injEq, heq, ↓reduceIte]
      have ⟨array', hArray'⟩ := ctxWf.opChain block' (by grind [IRContext.WellFormed])
      simp only [BlockPtr.operationList_iff_BlockPtr_OpChain.mp
        (BlockPtr.opChain_detachOpIfAttached_other hArray hArray' hparent (by grind))]
      simp [BlockPtr.operationList_iff_BlockPtr_OpChain.mp hArray]

end detachOpIfAttached

section setAttributes

theorem OperationPtr.setAttributes_WellFormed (ctx : IRContext OpInfo) (op : OperationPtr)
    (hctx : ctx.WellFormed) (hop : op.InBounds ctx) (newAttrs : DictionaryAttr) :
    (op.setAttributes ctx newAttrs hop).WellFormed := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx
  constructor
  · grind
  · intro val hval
    have ⟨array, harray⟩ := h₂ val (by grind)
    exists array
    simp only [Std.ExtHashSet.filter_empty] at harray ⊢
    apply ValuePtr.DefUse.unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro blk hblk
    have ⟨array, harray⟩ := h₃ blk (by grind)
    exists array
    simp only [Std.ExtHashSet.filter_empty] at harray ⊢
    apply BlockPtr.DefUse.unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro blk hblk
    have ⟨array, harray⟩ := h₄ blk (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro reg hreg
    have ⟨array, harray⟩ := h₅ reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro op' hop'
    have h_wf := h₆ op' (by grind)
    apply OperationPtr.WellFormed_unchanged h_wf (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro blk hblk
    have h_wf := h₇ blk (by grind)
    apply BlockPtr.WellFormed_unchanged h_wf (ctx' := op.setAttributes ctx newAttrs hop) <;> grind
  · intro reg hreg
    have h_wf := h₈ reg (by grind)
    apply RegionPtr.WellFormed_unchanged h_wf (ctx' := op.setAttributes ctx newAttrs hop) <;> grind

theorem BlockPtr.opChain_OperationPtr_setAttributes
    (hWf : BlockPtr.OpChain block' ctx array)
    {op : OperationPtr} (hop : op.InBounds ctx) (newAttrs : DictionaryAttr) :
    BlockPtr.OpChain block' (op.setAttributes ctx newAttrs hop) array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

@[grind =]
theorem BlockPtr.operationList_operationPtr_setAttributes
    (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' (OperationPtr.setAttributes op ctx newAttrs hop) newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
  grind [BlockPtr.opChain_OperationPtr_setAttributes]

end setAttributes

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
    have := @Rewriter.detachOperands.loop_wellFormed _ _ ctx missingOperands missingSuccessors
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
    have := @Rewriter.detachBlockOperands.loop_wellFormed _ _ ctx missingOperands missingSuccessors
      (op.getNumSuccessors ctx - 1) op hCtx hOp (by grind) wf (by grind)
    grind [Nat.toList_rcc_eq_toList_rco]

theorem BlockPtr.opChain_rewriter_detachOperands_loop
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block'
      (Rewriter.detachOperands.loop ctx op index hCtx hOp hIndex) array := by
  induction index generalizing ctx
  case zero =>
    simp only [Rewriter.detachOperands.loop]
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  case succ index ih =>
    simp only [Rewriter.detachOperands.loop]
    apply ih
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationList_rewriter_detachOperands_loop (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' (Rewriter.detachOperands.loop ctx op index hCtx hOp hIndex)
      newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
  grind [BlockPtr.opChain_rewriter_detachOperands_loop]

grind_pattern BlockPtr.operationList_rewriter_detachOperands_loop =>
  (Rewriter.detachOperands.loop ctx op index hCtx hOp hIndex).WellFormed,
  block'.operationList (Rewriter.detachOperands.loop ctx op index hCtx hOp hIndex) newCtxWf blockInBounds'

theorem BlockPtr.opChain_rewriter_detachOperands
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block' (Rewriter.detachOperands ctx op hCtx hOp) array := by
  simp only [Rewriter.detachOperands]
  split
  · exact hWf
  · exact BlockPtr.opChain_rewriter_detachOperands_loop hWf

theorem BlockPtr.operationList_rewriter_detachOperands (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' (Rewriter.detachOperands ctx op hCtx hOp)
      newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
  grind [BlockPtr.opChain_rewriter_detachOperands]

grind_pattern BlockPtr.operationList_rewriter_detachOperands =>
  (Rewriter.detachOperands ctx op hCtx hOp).WellFormed,
  block'.operationList (Rewriter.detachOperands ctx op hCtx hOp) newCtxWf blockInBounds'

theorem BlockPtr.opChain_rewriter_detachBlockOperands_loop
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block'
      (Rewriter.detachBlockOperands.loop ctx op index hCtx hOp hIndex) array := by
  induction index generalizing ctx
  case zero =>
    simp only [Rewriter.detachBlockOperands.loop]
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  case succ index ih =>
    simp only [Rewriter.detachBlockOperands.loop]
    apply ih
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationList_rewriter_detachBlockOperands_loop (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' (Rewriter.detachBlockOperands.loop ctx op index hCtx hOp hIndex)
      newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
  grind [BlockPtr.opChain_rewriter_detachBlockOperands_loop]

grind_pattern BlockPtr.operationList_rewriter_detachBlockOperands_loop =>
  (Rewriter.detachBlockOperands.loop ctx op index hCtx hOp hIndex).WellFormed,
  block'.operationList (Rewriter.detachBlockOperands.loop ctx op index hCtx hOp hIndex) newCtxWf blockInBounds'

theorem BlockPtr.opChain_rewriter_detachBlockOperands
    (hWf : BlockPtr.OpChain block' ctx array) :
    BlockPtr.OpChain block' (Rewriter.detachBlockOperands ctx op hCtx hOp) array := by
  simp only [Rewriter.detachBlockOperands]
  split
  · exact hWf
  · exact BlockPtr.opChain_rewriter_detachBlockOperands_loop hWf

theorem BlockPtr.operationList_rewriter_detachBlockOperands (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' (Rewriter.detachBlockOperands ctx op hCtx hOp)
      newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  simp only [←BlockPtr.operationList_iff_BlockPtr_OpChain]
  grind [BlockPtr.opChain_rewriter_detachBlockOperands]

grind_pattern BlockPtr.operationList_rewriter_detachBlockOperands =>
  (Rewriter.detachBlockOperands ctx op hCtx hOp).WellFormed,
  block'.operationList (Rewriter.detachBlockOperands ctx op hCtx hOp) newCtxWf blockInBounds'

theorem OpResultPtr.firstUse!_OpOperandPtr_removeFromCurrent_eq_none_of_firstUse!_eq_none
    (hctx : ctx.WellFormed missingUses missingSuccessors) :
    operand ∉ missingUses →
    result.InBounds ctx →
    (OpResultPtr.get! result ctx).firstUse = none →
    (OpResultPtr.get! result (OpOperandPtr.removeFromCurrent ctx operand operandIn ctxIn)).firstUse = none := by
  intro hmissing resultIn h
  have ⟨useArray, hUseArray⟩ := hctx.valueDefUseChains result (by grind)
  have ⟨useArray', hUseArray'⟩ := hctx.valueDefUseChains (operand.get! ctx).value (by grind)
  have hne : result ≠ (operand.get! ctx).value := by grind [ValuePtr.DefUse]
  have : useArray = #[] := by grind [ValuePtr.DefUse.getFirstUse!_none_iff hUseArray]
  have operandInArray : operand ∈ useArray' := by grind [ValuePtr.DefUse]
  have := ValuePtr.defUse_removeFromCurrent_other hne hUseArray hUseArray' (hvalue := operandInArray) (ctxInBounds := by grind)
  grind [ValuePtr.DefUse.getFirstUse!_none_iff this]

theorem OpResultPtr.firstUse!_detachOperands_loop_eq_none_of_firstUse!_eq_none
    (hctx : ctx.WellFormed missingUses missingSuccessors)
    (hMissingUses : ∀ i, i <= idx → (OpOperandPtr.mk operation i) ∉ missingUses)
    (resIn : result.InBounds ctx) :
    (OpResultPtr.get! result ctx).firstUse = none →
    (OpResultPtr.get! result (Rewriter.detachOperands.loop ctx operation idx hctxin hop hidx)).firstUse = none := by
  intro h
  induction idx generalizing ctx missingUses
  case zero =>
    simp only [Rewriter.detachOperands.loop]
    apply OpResultPtr.firstUse!_OpOperandPtr_removeFromCurrent_eq_none_of_firstUse!_eq_none hctx <;> grind
  case succ idx hi =>
    simp only [Rewriter.detachOperands.loop, Nat.succ_eq_add_one]
    apply hi
    · apply IRContext.wellFormed_OpOperandPtr_removeFromCurrent (missingOperandUses := missingUses) (by grind) hctx
    · grind
    · grind
    · apply OpResultPtr.firstUse!_OpOperandPtr_removeFromCurrent_eq_none_of_firstUse!_eq_none hctx <;> grind

theorem OpResultPtr.firstUse!_detachOperands_eq_none_of_firstUse!_eq_none
    (hctx : ctx.WellFormed missingUses missingSuccessors)
    (hMissingUses : ∀ i, (OpOperandPtr.mk operation i) ∉ missingUses)
    (resIn : result.InBounds ctx) :
    (OpResultPtr.get! result ctx).firstUse = none →
    (OpResultPtr.get! result (Rewriter.detachOperands ctx operation hctxin hop)).firstUse = none := by
  intro h
  simp only [Rewriter.detachOperands]
  split; grind
  apply OpResultPtr.firstUse!_detachOperands_loop_eq_none_of_firstUse!_eq_none hctx (by grind) resIn h

theorem Rewriter.eraseOp_WellFormed (ctx : IRContext OpInfo) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (noRegions : op.getNumRegions! ctx = 0)
    (noUses : op.hasUses! ctx = false)
    (hop : op.InBounds ctx) :
    (Rewriter.eraseOp ctx op hctx hop).WellFormed := by
  have hCtx₀ := detachOpIfAttached_WellFormed ctx wf (by grind) op (by grind)
  have hCtx₁ := detachOperands_wellFormed (op := op) (hOp := by grind) hCtx₀ (by grind) (hCtx := by grind)
  have hCtx₂ := detachBlockOperands_wellFormed (op := op) (hOp := by grind) hCtx₁ (by grind) (hCtx := by grind)
  simp only [Rewriter.eraseOp]
  apply IRContext.wellFormed_OperationPtr_dealloc
  · apply cast (a := hCtx₂); congr
    · simp only [Std.ExtHashSet.fromOperands]
      grind [Std.ExtHashSet.insertMany_empty_eq_ofList, OperationPtr.getOpOperand_def]
    · simp only [Std.ExtHashSet.fromSuccessors]
      grind [Std.ExtHashSet.insertMany_empty_eq_ofList, OperationPtr.getBlockOperand_def]
  · simp only [←OperationPtr.hasUses!_eq_hasUses]
    simp only [Bool.not_eq_true]
    simp only [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false]
    simp only [OperationPtr.getNumResults!_detachBlockOperands,
      OperationPtr.getNumResults!_detachOperands, OperationPtr.getNumResults!_detachOpIfAttached]
    intro index hindex
    simp only [ValuePtr.hasUses!_def]
    simp only [ValuePtr.getFirstUse!_detachBlockOperands, ValuePtr.getFirstUse!_opResult_eq,
      Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    apply OpResultPtr.firstUse!_detachOperands_eq_none_of_firstUse!_eq_none hCtx₀
    · grind
    · grind
    · simp only [OperationPtr.hasUses!_eq_false_iff_hasUses!_getResult_eq_false] at noUses
      simp [ValuePtr.hasUses!_def] at noUses
      grind
  · grind
  · grind

theorem BlockPtr.operationList_rewriter_eraseOp
    (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block (Rewriter.eraseOp ctx op hctx hop) hctx' hblock =
    if (op.get! ctx).parent = block then
      (BlockPtr.operationList block ctx ctxWf).erase op
    else
      BlockPtr.operationList block ctx ctxWf := by
  -- The op-chain change happens entirely in the first step (`detachOpIfAttached`); the remaining
  -- steps (`detachOperands`, `detachBlockOperands`, `dealloc`) leave every block's chain untouched.
  have hWf0 := Rewriter.detachOpIfAttached_WellFormed ctx ctxWf (by grind) op (by grind)
  have hWf1 := Rewriter.detachOperands_wellFormed (op := op) (hOp := by grind) hWf0 (by grind)
    (hCtx := by grind)
  have hWf2 := Rewriter.detachBlockOperands_wellFormed (op := op) (hOp := by grind) hWf1 (by grind)
    (hCtx := by grind)
  apply BlockPtr.operationList_iff_BlockPtr_OpChain.mp
  simp only [Rewriter.eraseOp]
  refine BlockPtr.opChain_OperationPtr_dealloc ?wf ?chain (by grind) (by grind)
  case wf =>
    apply cast (a := hWf2); congr
    · simp only [Std.ExtHashSet.fromOperands]
      grind [Std.ExtHashSet.insertMany_empty_eq_ofList, OperationPtr.getOpOperand_def]
    · simp only [Std.ExtHashSet.fromSuccessors]
      grind [Std.ExtHashSet.insertMany_empty_eq_ofList, OperationPtr.getBlockOperand_def]
  case chain =>
    grind [BlockPtr.operationList_rewriter_detachOpIfAttached,
      BlockPtr.opChain_rewriter_detachOperands,
      BlockPtr.opChain_rewriter_detachBlockOperands]

set_option warn.sorry false in
theorem OperationPtr.getOperand_Rewriter_eraseOp
    (heq : Rewriter.eraseOp ctx op hctx hop = newCtx) (hne : op ≠ op'):
    OperationPtr.getOperand op' newCtx idx inBounds idxInBounds =
    OperationPtr.getOperand op' ctx idx (by sorry) (by sorry) := by
  sorry

theorem Rewriter.createEmptyOp_wellFormed  (hctx : IRContext.WellFormed ctx) :
    Rewriter.createEmptyOp ctx opType properties = some (newCtx, newOp) →
    newCtx.WellFormed := by
  intro h
  constructor
  case inBounds => grind
  case valueDefUseChains =>
    intro valuePtr valuePtrInBounds
    have ⟨array, harray⟩ := hctx.valueDefUseChains valuePtr (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    intro blockPtr blockPtrInBounds
    have ⟨array, harray⟩ := hctx.blockDefUseChains blockPtr (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  case opChain =>
    intro blockPtr blockPtrInBounds
    have ⟨array, harray⟩ := hctx.opChain blockPtr (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  case blockChain =>
    intro reg hreg
    have ⟨array, harray⟩ := hctx.blockChain reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged (ctx := ctx) <;> grind
  case operations =>
    intro opPtr opPtrInBounds
    by_cases opPtr = newOp
    · constructor <;> grind
    · have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx.operations opPtr (by grind)
      constructor
      case neg.region_parent =>
        intro region regionInBounds
        apply OperationPtr.WellFormed.region_parent.unchanged (ctx := ctx) <;> grind
      all_goals grind
  case blocks =>
    intro bl hbl
    have := hctx.blocks bl (by grind)
    apply BlockPtr.WellFormed_unchanged (ctx := ctx) <;> grind
  case regions =>
    intro reg hreg
    have := hctx.regions reg (by grind)
    apply RegionPtr.WellFormed_unchanged (ctx := ctx) <;> try grind

theorem BlockPtr.opChain_rewriter_createEmptyOp
    (hWf : BlockPtr.OpChain block' ctx array)
    (h : Rewriter.createEmptyOp ctx opType properties = some (newCtx, newOp)) :
    BlockPtr.OpChain block' newCtx array := by
  apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind

theorem BlockPtr.operationList_rewriter_createEmptyOp
    (h : Rewriter.createEmptyOp ctx opType properties = some (newCtx, newOp))
    (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block' newCtx newCtxWf blockInBounds' =
    BlockPtr.operationList block' ctx ctxWf (by grind) := by
  have := BlockPtr.opChain_rewriter_createEmptyOp (block' := block')
    (array := block'.operationList ctx ctxWf (by grind))
    (by grind [BlockPtr.operationListWF]) h
  grind

grind_pattern BlockPtr.operationList_rewriter_createEmptyOp =>
  Rewriter.createEmptyOp ctx opType properties, some (newCtx, newOp),
  block'.operationList newCtx newCtxWf blockInBounds'

theorem Rewriter.createOp_WellFormed
    (hctx : IRContext.WellFormed ctx) :
    Rewriter.createOp ctx opType resultTypes operands blockOperands
      regions properties insertionPoint h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp) →
    newCtx.WellFormed := by
  simp only [createOp]
  split; grind
  rename_i ctx₁ newOp hNewOp
  have : ctx₁.WellFormed := by grind [Rewriter.createEmptyOp_wellFormed]
  split; grind
  rename_i ctx₂ hctx₂
  have : ctx₂.WellFormed :=
    by grind [Rewriter.initOpRegions_WellFormed, IRContext.wellFormed_rewriter_initOpResults]
  grind [insertOp?_WellFormed, Rewriter.initOpOperands_WellFormed,
    Rewriter.initBlockOperands_WellFormed]

theorem BlockPtr.operationList_rewriter_createOp
    (h : Rewriter.createOp ctx opType resultTypes operands blockOperands
      regions properties insertionPoint h₁ h₂ h₃ h₄ h₅ = some (newCtx, newOp))
    (ctxWf : ctx.WellFormed) :
    BlockPtr.operationList block newCtx newCtxWf blockIn =
    match insertionPoint with
    | none => BlockPtr.operationList block ctx ctxWf (by grind)
    | some ip =>
      if hb : ip.block! ctx = some block then
        (BlockPtr.operationList block ctx ctxWf (by grind)).insertIdx
          (ip.idxIn ctx block (by grind [Option.maybe_def]) (by grind [Option.maybe_def]) ctxWf)
          newOp (by apply InsertPoint.idxIn.le_size_operationList)
      else
        BlockPtr.operationList block ctx ctxWf (by grind) := by
  simp only [Rewriter.createOp] at h
  split at h; grind; rename_i ctx₂ newOp' hctx₂
  have ctx₂Wf : ctx₂.WellFormed := by grind [Rewriter.createEmptyOp_wellFormed]
  split at h; grind; rename_i ctx₃ hctx₃
  have ctx₃Wf : ctx₃.WellFormed := by grind [Rewriter.initOpRegions_WellFormed, IRContext.wellFormed_rewriter_initOpResults]
  cases insertionPoint with
  | none =>
    grind [Rewriter.initOpOperands_WellFormed, IRContext.wellFormed_rewriter_initOpResults]
  | some ip =>
    simp at h
    split at h; grind; rename_i ctx₄ hctx₄
    have ctx₄Wf : ctx₄.WellFormed := by
      grind [Rewriter.initOpOperands_WellFormed, Rewriter.initBlockOperands_WellFormed, Rewriter.insertOp?_WellFormed]
    simp at h; have ⟨_, _⟩ := h; subst newCtx newOp'
    simp
    rw [BlockPtr.operationList_rewriter_insertOp? hctx₄ (by grind [Rewriter.initOpOperands_WellFormed, Rewriter.initBlockOperands_WellFormed])]
    cases ip
    case before op =>
      simp only [InsertPoint.block!_before_eq, OperationPtr.parent!_initBlockOperands,
        OperationPtr.parent!_initOpOperands, InsertPoint.idxIn_before_eq]
      simp only [OperationPtr.parent!_initOpRegions hctx₃, OperationPtr.parent!_initOpResults,
        OperationPtr.parent!_createEmptyOp hctx₂, show op ≠ newOp by grind, ↓reduceIte]
      split <;>
        grind [Rewriter.initOpOperands_WellFormed, Rewriter.initBlockOperands_WellFormed,
          Rewriter.insertOp?_WellFormed, IRContext.wellFormed_rewriter_initOpResults]
    case atEnd b =>
      simp only [InsertPoint.block!_atEnd_eq, Option.some.injEq]
      split <;>
        grind [Rewriter.initOpOperands_WellFormed, Rewriter.initBlockOperands_WellFormed,
          Rewriter.insertOp?_WellFormed, IRContext.wellFormed_rewriter_initOpResults]

end Veir
