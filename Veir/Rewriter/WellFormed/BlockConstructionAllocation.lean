module

public import Veir.Rewriter.GetSet
public import Veir.IR.WellFormed
public import Veir.Rewriter.WellFormed.BlockConstruction

public section

namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx ctx' : IRContext OpInfo}

theorem BlockPtr.allocEmptyAtAddress_preserves_operation_wellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (op : OperationPtr) (hop : op.InBounds ctx') :
    op.WellFormed ctx' hop := by
  have hold : op.InBounds ctx := by grind
  apply OperationPtr.WellFormed_unchanged (wf.operations op hold) <;> grind

theorem BlockPtr.allocEmptyAtAddress_preserves_block_wellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (block : BlockPtr) (hblock : block.InBounds ctx') (hne : block ≠ newBlock) :
    block.WellFormed ctx' hblock := by
  have hold : block.InBounds ctx := by grind
  apply BlockPtr.WellFormed_unchanged (wf.blocks block hold) <;> grind

theorem BlockPtr.allocEmptyAtAddress_preserves_region_wellFormed
    (wf : ctx.WellFormed) (hfields : ctx'.FieldsInBounds)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (region : RegionPtr) (hregion : region.InBounds ctx') :
    region.WellFormed ctx' := by
  have hold : region.InBounds ctx := by grind
  apply RegionPtr.WellFormed_unchanged (wf.regions region hold) <;> grind

theorem BlockPtr.allocEmptyAtAddress_preserves_valueDefUse
    (wf : ctx.WellFormed)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (value : ValuePtr) (hvalue : value.InBounds ctx') :
    ∃ array, value.DefUse ctx' array := by
  obtain ⟨array, harray⟩ := wf.valueDefUseChains value (by grind)
  refine ⟨array, ?_⟩
  simp only [Std.ExtHashSet.filter_empty] at harray
  apply ValuePtr.DefUse.unchanged harray <;> grind

theorem BlockPtr.allocEmptyAtAddress_preserves_blockDefUse
    (wf : ctx.WellFormed)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (block : BlockPtr) (hblock : block.InBounds ctx') :
    ∃ array, block.DefUse ctx' array := by
  by_cases heq : block = newBlock
  · subst block
    refine ⟨#[], ?_⟩
    constructor <;> grind [Block.empty]
  obtain ⟨array, harray⟩ := wf.blockDefUseChains block (by grind)
  refine ⟨array, ?_⟩
  simp only [Std.ExtHashSet.filter_empty] at harray
  apply BlockPtr.DefUse.unchanged harray <;> grind

theorem BlockPtr.allocEmptyAtAddress_preserves_opChain
    (wf : ctx.WellFormed)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (block : BlockPtr) (hblock : block.InBounds ctx') :
    ∃ array, block.OpChain ctx' array := by
  by_cases heq : block = newBlock
  · subst block
    refine ⟨#[], ?_⟩
    constructor <;> grind [Block.empty]
  obtain ⟨array, harray⟩ := wf.opChain block (by grind)
  refine ⟨array, ?_⟩
  apply BlockPtr.OpChain_unchanged harray <;> grind [Block.empty]

theorem BlockPtr.allocEmptyAtAddress_preserves_blockChain
    (wf : ctx.WellFormed)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock))
    (region : RegionPtr) (hregion : region.InBounds ctx') :
    ∃ array, region.BlockChain ctx' array := by
  obtain ⟨array, harray⟩ := wf.blockChain region (by grind)
  refine ⟨array, ?_⟩
  apply RegionPtr.blockChain_unchanged harray <;> grind [Block.empty]

theorem BlockPtr.allocEmptyAtAddress_constructionWellFormed
    (wf : ctx.WellFormed)
    (halloc : BlockPtr.allocEmptyAtAddress ctx ca addr = some (ctx', newBlock)) :
    BlockConstructionWellFormed ctx' newBlock ∅ ∅ := by
  have hfields : ctx'.FieldsInBounds := BlockPtr.allocEmptyAtAddress_fieldsInBounds halloc wf.inBounds
  refine ⟨hfields, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Std.ExtHashSet.filter_empty] using
      allocEmptyAtAddress_preserves_valueDefUse wf halloc
  · simpa only [Std.ExtHashSet.filter_empty] using
      allocEmptyAtAddress_preserves_blockDefUse wf halloc
  · exact allocEmptyAtAddress_preserves_opChain wf halloc
  · exact allocEmptyAtAddress_preserves_blockChain wf halloc
  · exact allocEmptyAtAddress_preserves_operation_wellFormed wf hfields halloc
  · intro block hb
    by_cases h : block = newBlock
    · subst block
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> grind [Block.empty]
    · exact BlockPtr.BlockConstructionWellFormed.of_wellFormed
        (allocEmptyAtAddress_preserves_block_wellFormed wf hfields halloc block hb h)
  · exact allocEmptyAtAddress_preserves_region_wellFormed wf hfields halloc

theorem Sim.BlockPtr.allocEmpty_constructionWellFormed
    [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
    {ctx ctx' : Sim.IRContext OpInfo}
    (wf : ctx.spec.WellFormed)
    (halloc : Sim.BlockPtr.allocEmpty ctx ca = some (newBlock, ctx')) :
    BlockConstructionWellFormed ctx'.spec newBlock.spec ∅ ∅ := by
  exact BlockPtr.allocEmptyAtAddress_constructionWellFormed wf
    (Sim.BlockPtr.allocEmpty_spec' ca halloc)

end Veir
