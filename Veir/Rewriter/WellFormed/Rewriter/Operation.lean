import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic
import Veir.Rewriter.GetSetInBounds
import Veir.Rewriter.InsertPoint

namespace Veir

section InsertOp

unseal Rewriter.insertOp? in
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
    apply BlockPtr.DefUse_unchanged (ctx := ctx) <;> grind
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

end InsertOp

theorem Rewriter.detachOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hIn : op.InBounds ctx)
    (hasParent : (op.get ctx hIn).parent.isSome)
    (newCtx : IRContext) :
    Rewriter.detachOp ctx op hctx hIn hasParent = newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_detachOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.detachOp ctx op hctx hIn hasParent) ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

theorem Rewriter.eraseOp_WellFormed (ctx : IRContext) (wf : ctx.WellFormed)
    (hctx : ctx.FieldsInBounds) (op : OperationPtr)
    (hop : op.InBounds ctx)
    (hasParent : (op.get ctx hop).parent.isSome)
    (newCtx : IRContext) :
    Rewriter.eraseOp ctx op hctx hop hasParent = newCtx →
    newCtx.WellFormed := by
  sorry

theorem BlockPtr.operationList_Rewriter_eraseOp
    (hWf : BlockPtr.operationList blockPtr ctx ctxWellFormed blockInBounds = array) :
      BlockPtr.operationList blockPtr (Rewriter.eraseOp ctx op hctx hop hasParent) ctxWellFormed' blockInBounds' =
      if blockPtr = blockPtr' then
        array.erase op
      else
        array := by
  sorry

theorem OperationPtr.getOperand_Rewriter_eraseOp
    (heq : Rewriter.eraseOp ctx op hctx hop hasParent = newCtx) (hne : op ≠ op'):
    OperationPtr.getOperand op' newCtx idx inBounds idxInBounds =
    OperationPtr.getOperand op' ctx idx (by sorry) (by sorry) := by
  sorry

end Veir
