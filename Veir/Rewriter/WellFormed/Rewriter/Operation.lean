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
    apply RegionPtr.BlockChainWellFormed_unchanged harray <;> grind
  case operations =>
    intros op hop
    have : op.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf⟩ := h₆ op this
    apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind
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
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    intros block hblock
    have ⟨array, harray⟩ := h₃ block (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
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
    apply RegionPtr.BlockChainWellFormed_unchanged harray <;> grind
  case operations =>
    intros op' hop'
    have : op'.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf⟩ := h₆ op' this
    apply Operation.WellFormed_unchanged (ctx := ctx) <;> grind
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    grind [Block.WellFormed_unchanged]
  case regions =>
    grind [Region.WellFormed_unchanged]

end detachOp

theorem Rewriter.eraseOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hop : op.InBounds ctx)
    (newCtx : IRContext) :
    Rewriter.eraseOp ctx op hctx hop = newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_eraseOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.eraseOp ctx op hctx hop) ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

theorem OperationPtr.getOperand_Rewriter_eraseOp
    (heq : Rewriter.eraseOp ctx op hctx hop = newCtx) (hne : op ≠ op'):
    OperationPtr.getOperand op' newCtx idx inBounds idxInBounds =
    OperationPtr.getOperand op' ctx idx (by sorry) (by sorry) := by
  sorry

end Veir
