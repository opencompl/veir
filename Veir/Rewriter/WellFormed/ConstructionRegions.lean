module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.WellFormed.Construction
import all Veir.Rewriter.Basic
import Veir.IR.WellFormed
import Veir.Rewriter.GetSet

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

set_option maxHeartbeats 1000000 in
omit [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo] in
theorem Rewriter.pushRegion_constructionWellFormed
    {ctx : IRContext OpInfo} {op region hop hregion hregionParent}
    (wf : ConstructionWellFormed ctx op ∅ ∅) :
    ConstructionWellFormed (Rewriter.pushRegion ctx op region hop hregion hregionParent) op ∅ ∅ := by
  refine ⟨by grind, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros valuePtr valuePtrInBounds
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.valueDefUseChains wf valuePtr (by grind)
    exists array
    apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.blockDefUseChains wf blockPtr (by grind)
    exists array
    apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.opChain wf blockPtr (by grind)
    exists array
    apply BlockPtr.OpChain_unchanged (ctx := ctx) <;> grind
  · intros reg hreg
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.blockChain wf reg (by grind)
    exists array
    apply RegionPtr.blockChain_unchanged (ctx := ctx) <;> grind
  · intros opPtr' opPtrInBounds
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
      IRContext.ConstructionWellFormed.operations wf opPtr' (by grind)
    refine ⟨by grind, by grind, by grind, by grind, by grind, by grind, ?_, by grind,
      by grind, by grind, by grind, by grind⟩
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
  · intros bl hbl
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := IRContext.ConstructionWellFormed.blocks wf bl (by grind)
    constructor <;> grind
  · intros reg hreg
    have ⟨h₁, h₂⟩ := IRContext.ConstructionWellFormed.regions wf reg (by grind)
    constructor
    · grind
    · simp only [RegionPtr.parent!_pushRegion]
      split
      · simp only [Option.some.injEq, forall_eq']
        exists op.getNumRegions! ctx
        grind
      · intro parent hparent
        have ⟨i, hi⟩ := h₂ hparent
        simp only [OperationPtr.getRegion!_pushRegion]
        grind

theorem Rewriter.initOpRegions_constructionWellFormed
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {regions index h₁ h₂ h₃ h₄ h₅}
    (wf : ConstructionWellFormed ctx.spec opPtr.spec ∅ ∅)
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    ConstructionWellFormed ctx'.spec opPtr.spec ∅ ∅ := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim
  case case1 =>
    cases Option.some.inj heq
    exact wf
  case case2 ctx0 index0 hop hregions hctx hn hcap h region hParent nextCtx ih =>
    apply ih _ heq
    simp only [nextCtx, pushRegionAt_def, pushRegionAtSim]
    exact pushRegion_constructionWellFormed wf
  case case3 => simp at heq

@[grind .]
theorem Rewriter.initOpRegions_preserves_numResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {regions index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    ptr.getNumResults! ctx'.spec = ptr.getNumResults! ctx.spec := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt_def, pushRegionAtSim]

@[grind .]
theorem Rewriter.initOpRegions_preserves_capResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {regions index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    (ptr.get! ctx'.spec).capResults = (ptr.get! ctx.spec).capResults := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt_def, pushRegionAtSim]

@[grind .]
theorem Rewriter.initOpRegions_preserves_capRegions (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {regions index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    (ptr.get! ctx'.spec).capRegions = (ptr.get! ctx.spec).capRegions := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt_def, pushRegionAtSim]

@[grind .]
theorem Rewriter.initOpRegions_numRegions
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {regions index h₁ h₂ h₃ h₄ h₅}
    (hindex : index.toNat ≤ regions.size)
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    opPtr.spec.getNumRegions! ctx'.spec = regions.size := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;>
    grind [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initOpRegions_preserves_parent (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {regions index h₁ h₂ h₃ h₄ h₅}
    (heq : Rewriter.initOpRegions opPtr ctx regions index h₁ h₂ h₃ h₄ h₅ = some ctx') :
    (ptr.get! ctx'.spec).parent = (ptr.get! ctx.spec).parent := by
  simp [initOpRegions_def] at heq
  fun_induction initOpRegionsSim <;> grind (gen := 20) [pushRegionAt_def, pushRegionAtSim]

end Veir
