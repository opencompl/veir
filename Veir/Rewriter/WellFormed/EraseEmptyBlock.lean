module

public import Veir.Rewriter.EraseContainers

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

attribute [local grind =] Option.maybe_def

/-- An empty, unused detached block has no incoming references, so its allocation may
    be logically deleted without assuming the post-deallocation field-bounds invariant. -/
theorem IRContext.fieldsInBounds_deallocEmptyBlock
    {ctx : IRContext OpInfo} (block : BlockPtr) (ib : block.InBounds ctx)
    (wf : ctx.WellFormed) (parent : (block.get! ctx).parent = none)
    (args : block.getNumArguments! ctx = 0)
    (ops : (block.get! ctx).firstOp = none)
    (uses : (block.get! ctx).firstUse = none) :
    (block.dealloc ctx).FieldsInBounds := by
  have noParent : ∀ op : OperationPtr, op.InBounds ctx → (op.get! ctx).parent ≠ some block := by
    obtain ⟨array, ha⟩ := wf.opChain block ib
    have hempty : array = #[] := by have := ha.first; grind
    intro op hi hp
    have := ha.allOpsInChain op hi hp
    simp [hempty] at this
  have noUse : ∀ use : BlockOperandPtr, use.InBounds ctx → (use.get! ctx).value ≠ block := by
    obtain ⟨array, ha⟩ := wf.blockDefUseChains block ib
    simp only [Std.ExtHashSet.filter_empty] at ha
    have hempty : array = #[] := by have := ha.firstElem; grind
    intro use hi hv
    have := ha.allUsesInChain use hi hv
    simp [hempty] at this
  have noBack : ∀ use : BlockOperandPtr, use.InBounds ctx →
      (use.get! ctx).back ≠ .blockFirstUse block := by
    intro use hi heq
    obtain ⟨array, ha⟩ := wf.blockDefUseChains (use.get! ctx).value (by grind)
    simp only [Std.ExtHashSet.filter_empty] at ha
    have hm : use ∈ array := (ha.allUsesInChain use hi rfl).mpr (by simp)
    obtain ⟨i, hlt, hget⟩ := Array.getElem_of_mem hm
    by_cases hz : i = 0
    · have hfirst : ((use.get! ctx).value.get! ctx).firstUse = some use := by
        have := ha.firstElem
        grind
      have := ha.firstUseBack hfirst
      have := noUse use hi
      grind
    · have := ha.backNextUse i (by omega) hlt
      grind
  have noArgument : ∀ arg : BlockArgumentPtr, arg.InBounds ctx → arg.block ≠ block := by
    grind [BlockArgumentPtr.inBounds_def]
  have noNextPrev : ∀ b : BlockPtr, b.InBounds ctx →
      (b.get! ctx).prev ≠ some block ∧ (b.get! ctx).next ≠ some block := by
    intro b hb
    have bwf := wf.blocks b hb
    cases hp : (b.get! ctx).parent with
    | none =>
      have := bwf.prev_eq_of_parent_eq_none hp
      have := bwf.next_eq_of_parent_eq_none hp
      grind
    | some region =>
      obtain ⟨array, ha⟩ := wf.blockChain region (by grind)
      have hm := ha.allBlocksInChain b hb hp
      obtain ⟨i, hi, he⟩ := Array.getElem_of_mem hm
      have notMem : block ∉ array := by intro hm; have := ha.opParent hm; grind
      constructor
      · intro hprev
        by_cases hz : i = 0
        · have hf : (region.get! ctx).firstBlock = some b := by have := ha.first; grind
          have := ha.prevFirst hf
          grind
        · have := ha.prev i (by omega) hi
          grind
      · intro hnext
        have := ha.next hi
        grind
  have noRegion : ∀ r : RegionPtr, r.InBounds ctx →
      (r.get! ctx).firstBlock ≠ some block ∧ (r.get! ctx).lastBlock ≠ some block := by
    intro r hr
    obtain ⟨array, ha⟩ := wf.blockChain r hr
    have notMem : block ∉ array := by intro hm; have := ha.opParent hm; grind
    have := ha.first
    have := ha.last
    grind
  have hfields := wf.inBounds
  constructor
  · intro op hi
    have old := hfields.operations_inBounds op (by grind)
    constructor
    · intro res hr he
      have oldRes := old.results_inBounds res (by grind) he
      constructor <;> grind [OpResult.FieldsInBounds]
    · grind [Operation.FieldsInBounds]
    · grind [Operation.FieldsInBounds]
    · grind [Operation.FieldsInBounds]
    · intro use hu he
      have oldUse := old.blockOperands_inBounds use (by grind) he
      constructor <;> grind [BlockOperand.FieldsInBounds, BlockOperandPtrPtr.InBounds,
        cases BlockOperandPtrPtr]
    · have hget := OperationPtr.get!_BlockPtr_dealloc hi
      have := OperationPtr.getNumRegions!_eq_of_OperationPtr_get!_eq hget
      have := OperationPtr.getRegion!_eq_of_OperationPtr_get!_eq hget
      grind [Operation.FieldsInBounds]
    · intro use hu he
      have oldUse := old.operands_inBounds use (by grind) he
      constructor <;> grind [OpOperand.FieldsInBounds, OpOperandPtrPtr.InBounds,
        ValuePtr.InBounds, cases OpOperandPtrPtr, cases ValuePtr]
  · intro b hb
    have old := hfields.blocks_inBounds b (by grind)
    constructor
    · grind [Block.FieldsInBounds]
    · grind [Block.FieldsInBounds]
    · grind [Block.FieldsInBounds]
    · grind [Block.FieldsInBounds]
    · grind [Block.FieldsInBounds]
    · grind [Block.FieldsInBounds]
    · intro arg ha he
      have oldArg := old.arguments_inBounds arg (by grind) he
      have := (wf.blocks b (by grind)).argument_owners arg.index (by grind [BlockArgumentPtr.inBounds_def])
      constructor <;> grind [BlockArgument.FieldsInBounds, BlockPtr.getArgument]
  · intro r hr
    have old := hfields.regions_inBounds r (by grind)
    constructor <;> grind [Region.FieldsInBounds]

end Veir
