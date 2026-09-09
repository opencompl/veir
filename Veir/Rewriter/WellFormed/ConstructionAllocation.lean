module

public import Veir.Rewriter.GetSet
public import Veir.IR.WellFormed
public import Veir.Rewriter.WellFormed.Construction

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : IRContext OpInfo}

theorem OperationPtr.allocEmptyAt_preserves_operation_wellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (op : OperationPtr) (hop : op.InBounds ctx') (hne : op ≠ newOp) :
    op.WellFormed ctx' hop := by
  have hold : op.InBounds ctx := by grind
  apply OperationPtr.WellFormed_unchanged (wf.operations op hold) <;> grind

theorem OperationPtr.allocEmptyAt_preserves_block_wellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (block : BlockPtr) (hblock : block.InBounds ctx') :
    block.WellFormed ctx' hblock := by
  have hold : block.InBounds ctx := by grind
  apply BlockPtr.WellFormed_unchanged (wf.blocks block hold) <;> grind

theorem OperationPtr.allocEmptyAt_preserves_region_wellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (region : RegionPtr) (hregion : region.InBounds ctx') :
    region.WellFormed ctx' := by
  have hold : region.InBounds ctx := by grind
  apply RegionPtr.WellFormed_unchanged (wf.regions region hold) <;> grind

theorem OperationPtr.allocEmptyAt_preserves_valueDefUse
    (wf : ctx.WellFormed)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (value : ValuePtr) (hvalue : value.InBounds ctx') :
    ∃ array, value.DefUse ctx' array := by
  obtain ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
  refine ⟨array, ?_⟩
  simp only [Std.ExtHashSet.filter_empty] at harray
  apply ValuePtr.DefUse.unchanged harray <;> grind

theorem OperationPtr.allocEmptyAt_preserves_blockDefUse
    (wf : ctx.WellFormed)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (block : BlockPtr) (hblock : block.InBounds ctx') :
    ∃ array, block.DefUse ctx' array := by
  obtain ⟨array, harray⟩ := wf.blockDefUseChains block (by grind)
  refine ⟨array, ?_⟩
  simp only [Std.ExtHashSet.filter_empty] at harray
  apply BlockPtr.DefUse.unchanged harray <;> grind

theorem OperationPtr.allocEmptyAt_preserves_opChain
    (wf : ctx.WellFormed)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (block : BlockPtr) (hblock : block.InBounds ctx') :
    ∃ array, block.OpChain ctx' array := by
  obtain ⟨array, harray⟩ := wf.opChain block (by grind)
  refine ⟨array, ?_⟩
  apply BlockPtr.OpChain_unchanged harray <;> grind [Operation.empty]

theorem OperationPtr.allocEmptyAt_preserves_blockChain
    (wf : ctx.WellFormed)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp))
    (region : RegionPtr) (hregion : region.InBounds ctx') :
    ∃ array, region.BlockChain ctx' array := by
  obtain ⟨array, harray⟩ := wf.blockChain region (by grind)
  refine ⟨array, ?_⟩
  apply RegionPtr.blockChain_unchanged harray <;> grind

theorem OperationPtr.allocEmptyAt_constructionWellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : OperationPtr.allocEmptyAt ctx ty properties cr cb cg co addr = some (ctx', newOp)) :
    ConstructionWellFormed ctx' newOp ∅ ∅ := by
  refine ⟨hfields, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.ExtHashSet.filter_empty] using
      allocEmptyAt_preserves_valueDefUse wf halloc
  · simpa only [Std.ExtHashSet.filter_empty] using
      allocEmptyAt_preserves_blockDefUse wf halloc
  · exact allocEmptyAt_preserves_opChain wf halloc
  · exact allocEmptyAt_preserves_blockChain wf halloc
  · intro op hop
    by_cases h : op = newOp
    · subst op
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        grind [Operation.empty]
    · exact OperationPtr.ConstructionWellFormed.of_wellFormed
        (allocEmptyAt_preserves_operation_wellFormed wf hfields halloc op hop h)
  · exact allocEmptyAt_preserves_block_wellFormed wf hfields halloc
  · exact allocEmptyAt_preserves_region_wellFormed wf hfields halloc

theorem Sim.OperationPtr.allocEmpty_constructionWellFormed
    [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
    {ctx ctx' : Sim.IRContext OpInfo}
    (wf : ctx.spec.WellFormed)
    (halloc : Sim.OperationPtr.allocEmpty ctx ty properties cr co cb cg h₁ h₂ h₃ h₄ = some (newOp, ctx')) :
    ConstructionWellFormed ctx'.spec newOp.spec ∅ ∅ := by
  exact OperationPtr.allocEmptyAt_constructionWellFormed wf ctx'.sim.fieldsInBounds
    (Sim.OperationPtr.allocEmpty_spec' halloc)

end Veir
