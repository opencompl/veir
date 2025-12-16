import Mlir.Core.Basic
import Mlir.Core.WellFormed
import Mlir.Rewriter.Basic

namespace Mlir

@[grind .]
theorem Rewriter.pushResult_WellFormed (ctx: IRContext) (opPtr: OperationPtr)
    (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx)
    (hres : newResult.FieldsInBounds (opPtr.pushResult ctx newResult hop))
    (hNoFirst : newResult.firstUse = none)
    (hIndex : newResult.index = opPtr.getNumResults ctx) :
    (opPtr.pushResult ctx newResult hop).WellFormed := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx
  constructor
  case inBounds =>
    grind
  case valueUseDefChains =>
    intros val hval
    by_cases heq : val = .opResult (opPtr.nextResult ctx)
    · subst heq
      exists #[]
      constructor <;> grind [ValuePtr.getFirstUse]
    · have ⟨array, harray⟩ := h₂ val (by grind)
      exists array
      apply @IRContext.ValuePtr_UseDefChainWellFormed_unchanged ctx <;> grind
  case blockUseDefChains =>
    intros bl hbl
    have ⟨array, harray⟩ := h₃ bl (by grind)
    exists array
    apply @IRContext.BlockPtr_UseDefChainWellFormed_unchanged ctx <;> grind
  case opChain =>
    intros op hop
    have ⟨array, harray⟩ := h₄ op (by grind)
    exists array
    apply @IRContext.OperationChainWellFormed_unchanged ctx <;>
      grind
  case blockChain =>
    intros rg hrg
    have ⟨array, harray⟩ := h₅ rg (by grind)
    exists array
    apply IRContext.BlockChainWellFormed_unchanged harray <;> grind
  case operations =>
    intros op hop
    have : op.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf⟩ := h₆ op this
    constructor
    -- TODO: Understand why grind fails here
    case region_parent => intros; constructor <;> simp <;> grind
    -- Add the necessary lemmas to not manually add lemmas to grind here
    all_goals grind [OperationPtr.getResult]
  case blocks =>
    intros bl hbl
    have : bl.InBounds ctx := by grind
    have ⟨ha, hb, hc⟩ := h₇ bl this
    constructor <;> grind
  case regions =>
    intros rg hrg
    have : rg.InBounds ctx := by grind
    have ⟨ha, hb⟩ := h₈ rg this
    constructor <;> grind

theorem Rewriter.initOpResults_WellFormed (ctx: IRContext) (opPtr: OperationPtr) (numResults: Nat)
    (index : Nat) (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx) (newCtx : IRContext) hIndex :
    Rewriter.initOpResults ctx opPtr numResults index hop hIndex = newCtx →
    newCtx.WellFormed := by
  induction numResults generalizing index ctx
  case zero =>
    grind [initOpResults]
  case succ nr ih =>
    unfold initOpResults
    lift_lets
    intros result ctx' h₁ h₂
    apply ih
    apply Rewriter.pushResult_WellFormed
    · assumption
    · assumption
    · grind
    · grind
