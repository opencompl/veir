module

public import Veir.IR.Buffed.InBounds
public import Veir.IR.WellFormed
public import Veir.Rewriter.GetSet

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

/-- Attribute dictionaries do not affect pointer topology or ownership. -/
theorem Sim.OperationPtr.setAttributes_wellFormed
    (ctx : Sim.IRContext OpInfo) (op : Sim.OperationPtr) (attrs : DictionaryAttr)
    (ib : op.InBounds ctx) {ctx' : Sim.IRContext OpInfo}
    (wf : ctx.spec.WellFormed) (h : op.setAttributes ctx attrs ib = some ctx') :
    ctx'.spec.WellFormed := by
  rw [Sim.OperationPtr.setAttributes_spec ctx op attrs ib h]
  constructor
  · grind
  · intro v hv
    obtain ⟨a, ha⟩ := wf.valueDefUseChains v (by grind)
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    refine ⟨a, ?_⟩
    apply ha.unchanged (by grind) <;> grind
  · intro b hb
    obtain ⟨a, ha⟩ := wf.blockDefUseChains b (by grind)
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    refine ⟨a, ?_⟩
    apply ha.unchanged (by grind) <;> grind
  · intro b hb
    obtain ⟨a, ha⟩ := wf.opChain b (by grind)
    refine ⟨a, ?_⟩
    apply BlockPtr.OpChain_unchanged ha (by grind) <;> grind
  · intro r hr
    obtain ⟨a, ha⟩ := wf.blockChain r (by grind)
    refine ⟨a, ?_⟩
    apply RegionPtr.blockChain_unchanged ha (by grind) <;> grind
  · intro o ho
    apply OperationPtr.WellFormed_unchanged (wf.operations o (by grind)) <;> grind
  · intro b hb
    apply BlockPtr.WellFormed_unchanged (wf.blocks b (by grind)) <;> grind
  · intro r hr
    apply RegionPtr.WellFormed_unchanged (wf.regions r (by grind)) <;> grind

end Veir
