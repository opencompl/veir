module

public import Veir.Buffered.Rewriter.LinkedList.WellFormed
public import Veir.Buffered.Rewriter.GetSet

public section
namespace Veir.Buffered

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

/-- Retargeting a successor which has been removed from its use list preserves the
    well-formedness invariant with that use marked missing. -/
theorem Sim.IRContext.wellFormed_BlockOperandPtr_setValue_missing
    {ctx : Sim.IRContext OpInfo} (use : Sim.BlockOperandPtr) (block : Sim.BlockPtr)
    (hu : use.InBounds ctx) (hb : block.InBounds ctx)
    (wf : ctx.spec.WellFormed ∅ (Std.ExtHashSet.ofList [use.spec])) :
    (use.setValue ctx block hu hb).spec.WellFormed ∅ (Std.ExtHashSet.ofList [use.spec]) := by
  constructor
  · exact (use.setValue ctx block hu hb).fieldsInBounds
  · intro value hv
    obtain ⟨array, ha⟩ := wf.valueDefUseChains value (by grind)
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    refine ⟨array, ?_⟩
    apply ha.unchanged (by grind) <;> grind
  · intro b hbi
    obtain ⟨array, ha⟩ := wf.blockDefUseChains b (by grind)
    have hnot : use.spec ∉ array := by
      intro hm
      have hvalue := ha.useValue use.spec hm
      have hh := (ha.allUsesInChain use.spec hu.ib hvalue).mp hm
      simp [hvalue] at hh
    refine ⟨array, ?_⟩
    simp only [Sim.BlockOperandPtr.setValue_spec]
    constructor <;> grind [BlockPtr.DefUse]
  · intro b hbi
    obtain ⟨array, ha⟩ := wf.opChain b (by grind)
    refine ⟨array, ?_⟩
    apply BlockPtr.OpChain_unchanged ha (by grind) <;> grind
  · intro r hri
    obtain ⟨array, ha⟩ := wf.blockChain r (by grind)
    refine ⟨array, ?_⟩
    apply RegionPtr.blockChain_unchanged ha (by grind) <;> grind
  · intro op hi
    simp only [Sim.BlockOperandPtr.setValue_spec]
    apply OperationPtr.WellFormed_unchanged (wf.operations op (by grind)) <;> grind
  · intro b hi
    simp only [Sim.BlockOperandPtr.setValue_spec]
    apply BlockPtr.WellFormed_unchanged (wf.blocks b (by grind)) <;> grind
  · intro r hi
    simp only [Sim.BlockOperandPtr.setValue_spec]
    apply RegionPtr.WellFormed_unchanged (wf.regions r (by grind)) <;> grind

/-- Redirect a single successor use, maintaining both reverse-use lists. -/
@[inline, expose]
def Rewriter.replaceBlockUse (ctx : Sim.IRContext OpInfo)
    (use : Sim.BlockOperandPtr) (block : Sim.BlockPtr)
    (hu : use.InBounds ctx) (hb : block.InBounds ctx) : Sim.IRContext OpInfo :=
  let ctx := use.removeFromCurrent ctx hu ctx.fieldsInBounds
  let ctx := use.setValue ctx block (by grind [generic_ptr_grind]) (by grind [generic_ptr_grind])
  use.insertIntoCurrent ctx (by grind [generic_ptr_grind]) ctx.fieldsInBounds

@[grind =]
theorem Rewriter.replaceBlockUse_inBounds (ctx : Sim.IRContext OpInfo)
    (use : Sim.BlockOperandPtr) (block : Sim.BlockPtr) hu hb (ptr : Sim.GenericPtr) :
    ptr.InBounds (replaceBlockUse ctx use block hu hb) ↔ ptr.InBounds ctx := by
  simp only [replaceBlockUse]
  grind

theorem Rewriter.replaceBlockUse_wellFormed (ctx : Sim.IRContext OpInfo)
    (use : Sim.BlockOperandPtr) (block : Sim.BlockPtr) hu hb
    (wf : ctx.spec.WellFormed) : (replaceBlockUse ctx use block hu hb).spec.WellFormed := by
  let ctx₁ := use.removeFromCurrent ctx hu ctx.fieldsInBounds
  have hu₁ : use.InBounds ctx₁ := by grind [generic_ptr_grind]
  have hb₁ : block.InBounds ctx₁ := by grind [generic_ptr_grind]
  have wf₁ : ctx₁.spec.WellFormed ∅ (Std.ExtHashSet.ofList [use.spec]) := by
    simpa [ctx₁] using Sim.IRContext.wellFormed_BlockOperandPtr_removeFromCurrent
      (use := use) (useInBounds := hu) (ctxInBounds := ctx.fieldsInBounds) (by simp) wf
  let ctx₂ := use.setValue ctx₁ block hu₁ hb₁
  have hu₂ : use.InBounds ctx₂ := by grind [generic_ptr_grind]
  have wf₂ := Sim.IRContext.wellFormed_BlockOperandPtr_setValue_missing use block hu₁ hb₁ wf₁
  have wf₃ := Sim.IRContext.wellFormed_BlockOperandPtr_insertIntoCurrent
    (ctx := ctx₂) (use := use) (useInBounds := hu₂) (ctxInBounds := ctx₂.fieldsInBounds)
    (by simp) wf₂
  have hempty : (Std.ExtHashSet.ofList [use.spec]).erase use.spec = ∅ := by
    ext x
    simp
  rw [hempty] at wf₃
  simpa [replaceBlockUse, ctx₁, ctx₂] using wf₃

end Veir.Buffered
