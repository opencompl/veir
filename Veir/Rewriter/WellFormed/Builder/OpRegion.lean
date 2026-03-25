import Veir.IR.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSetInBounds

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

theorem IRContext.wellFormed_Rewriter_pushRegion :
    ctx.WellFormed →
    (Rewriter.pushRegion ctx op region hop hregion hregionParent).WellFormed := by
  intro wf
  constructor
  case valueDefUseChains =>
    intros valuePtr valuePtrInBounds
    have ⟨array, arrayWf⟩ := wf.valueDefUseChains valuePtr (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  case blockDefUseChains =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := wf.blockDefUseChains blockPtr (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  case inBounds => grind
  case opChain =>
    intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := wf.opChain blockPtr (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;>
      grind
  case blockChain =>
    intros reg hreg
    have ⟨array, arrayWf⟩ := wf.blockChain reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged (ctx := ctx) <;>
      grind
  case operations =>
    intros opPtr' opPtrInBounds
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := wf.operations opPtr' (by grind)
    constructor
    case region_parent =>
      intros region' region'InBounds
      constructor
      · grind
      · simp only [RegionPtr.parent!_pushRegion]
        split; rotate_left
        · simp only [OperationPtr.getRegion!_pushRegion]
          grind
        · intro _
          exists op.getNumRegions! ctx
          grind
    all_goals grind [Operation.WellFormed]
  case blocks =>
    intros bl hbl
    have ⟨h₁, h₂, h₃, h₄, h₅⟩ := wf.blocks bl (by grind)
    constructor <;> grind
  case regions =>
    intros reg hreg
    have ⟨h₁, h₂⟩ := wf.regions reg (by grind)
    constructor
    · grind [Rewriter.pushOperand]
    · simp only [RegionPtr.parent!_pushRegion]
      split
      · simp only [Option.some.injEq, forall_eq']
        exists op.getNumRegions! ctx
        grind
      · intro parent hparent
        have ⟨i, hi⟩ := h₂ hparent
        simp only [OperationPtr.getRegion!_pushRegion]
        grind

theorem Rewriter.initOpRegions_WellFormed (opPtr: OperationPtr)
    (hop : opPtr.InBounds ctx) (hfields : ctx.FieldsInBounds) (hctx : IRContext.WellFormed ctx) {hn}
    {ctx' : IRContext OpInfo}
    (h : Rewriter.initOpRegions ctx opPtr regions n hop regionInBounds hfields hn = some ctx') :
    ctx'.WellFormed := by
  fun_induction Rewriter.initOpRegions
  case case1 => grind
  case case2 => grind [IRContext.wellFormed_Rewriter_pushRegion]
  case case3 => grind
