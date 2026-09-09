module

public import Veir.Rewriter.Basic
public import Veir.IR.WellFormed
import all Veir.Rewriter.Basic
import Veir.Rewriter.GetSet

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

set_option maxHeartbeats 1000000 in
/-- Allocating a fresh, detached empty region preserves all IR invariants. -/
theorem RegionPtr.allocEmptyAt_wellFormed
    {ctx ctx' : IRContext OpInfo}
    (wf : ctx.WellFormed)
    (halloc : RegionPtr.allocEmptyAt ctx addr = some (ctx', region)) :
    ctx'.WellFormed := by
  have hfields : ctx'.FieldsInBounds := by grind
  constructor
  case inBounds => exact hfields
  case valueDefUseChains =>
    intro v hv
    obtain ⟨a, ha⟩ := wf.valueDefUseChains v (by grind)
    exists a
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    apply ValuePtr.DefUse.unchanged ha <;> grind
  case blockDefUseChains =>
    intro b hb
    obtain ⟨a, ha⟩ := wf.blockDefUseChains b (by grind)
    exists a
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    apply BlockPtr.DefUse.unchanged ha <;> grind
  case opChain =>
    intro b hb
    obtain ⟨a, ha⟩ := wf.opChain b (by grind)
    exists a
    apply BlockPtr.OpChain_unchanged ha <;> grind
  case blockChain =>
    intro r hr
    by_cases he : r = region
    · subst r
      exists #[]
      constructor <;> grind [Region.empty]
    · obtain ⟨a, ha⟩ := wf.blockChain r (by grind)
      exists a
      apply RegionPtr.blockChain_unchanged ha <;> grind
  case operations =>
    intro o ho
    apply OperationPtr.WellFormed_unchanged (wf.operations o (by grind)) <;> grind [Region.empty]
  case blocks =>
    intro b hb
    apply BlockPtr.WellFormed_unchanged (wf.blocks b (by grind)) <;> grind
  case regions =>
    intro r hr
    by_cases he : r = region
    · subst r
      constructor <;> grind [Region.empty]
    · apply RegionPtr.WellFormed_unchanged (wf.regions r (by grind)) <;> grind

theorem Sim.RegionPtr.allocEmpty_wellFormed
    [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
    {ctx ctx' : Sim.IRContext OpInfo}
    (wf : ctx.spec.WellFormed)
    (halloc : Sim.RegionPtr.allocEmpty ctx = some (region, ctx')) :
    ctx'.spec.WellFormed := by
  exact Veir.RegionPtr.allocEmptyAt_wellFormed wf (Sim.RegionPtr.allocEmpty_spec' halloc)

/-- Successful region creation preserves full well-formedness. -/
theorem Rewriter.createRegion_wellFormed
    [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
    {ctx ctx' : Sim.IRContext OpInfo}
    (wf : ctx.spec.WellFormed)
    (hcreate : Rewriter.createRegion ctx = some (ctx', region)) :
    ctx'.spec.WellFormed := by
  simp only [createRegion_def, createRegionSim] at hcreate
  split at hcreate
  · simp at hcreate
  · simp only [Option.some.injEq, Prod.mk.injEq] at hcreate
    obtain ⟨rfl, rfl⟩ := hcreate
    exact Sim.RegionPtr.allocEmpty_wellFormed wf (by assumption)

end Veir
