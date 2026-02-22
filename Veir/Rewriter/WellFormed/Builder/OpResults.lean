import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.Basic

namespace Veir

variable {opInfo : Type} [OpInfo opInfo]
variable {ctx : IRContext opInfo}

@[grind .]
theorem Rewriter.pushResult_WellFormed {newResult} (ctx: IRContext opInfo) (opPtr: OperationPtr)
    (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx)
    (hres : newResult.FieldsInBounds (opPtr.pushResult ctx newResult hop))
    (hNoFirst : newResult.firstUse = none)
    (hIndex : newResult.index = opPtr.getNumResults ctx)
    (hOwner : newResult.owner = opPtr) :
    (opPtr.pushResult ctx newResult hop).WellFormed := by
  have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := hctx
  constructor
  case inBounds =>
    grind
  case valueDefUseChains =>
    intros val hval
    by_cases heq : val = .opResult (opPtr.nextResult ctx)
    · subst heq
      exists #[]
      constructor <;> grind [ValuePtr.getFirstUse]
    · have ⟨array, harray⟩ := h₂ val (by grind)
      exists array
      apply @ValuePtr.DefUse.unchanged _ _ ctx <;> grind
  case blockDefUseChains =>
    intros bl hbl
    have ⟨array, harray⟩ := h₃ bl (by grind)
    exists array
    apply @BlockPtr.DefUse.unchanged _ _ ctx <;> grind
  case opChain =>
    intros op hop
    have ⟨array, harray⟩ := h₄ op (by grind)
    exists array
    apply @BlockPtr.OpChain_unchanged _ _ ctx <;>
      grind
  case blockChain =>
    intros rg hrg
    have ⟨array, harray⟩ := h₅ rg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged harray <;> grind
  case operations =>
    intros op hop
    have : op.InBounds ctx := by grind
    have ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ := h₆ op this
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

theorem Rewriter.initOpResults_WellFormed (ctx: IRContext opInfo) (opPtr: OperationPtr) (resultTypes: Array TypeAttr)
    (index : Nat) (hop : opPtr.InBounds ctx) (hctx : IRContext.WellFormed ctx) (newCtx : IRContext opInfo) hIndex :
    Rewriter.initOpResults ctx opPtr resultTypes index hop hIndex = newCtx →
    newCtx.WellFormed := by
  induction h: resultTypes.size - index generalizing index ctx
  case zero =>
    grind [initOpResults]
  case succ nr ih =>
    unfold initOpResults
    split; grind
    lift_lets
    intros result ctx' heq
    have : result.FieldsInBounds ctx' := by constructor <;> grind
    grind
