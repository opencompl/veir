module

public import Veir.IR.WellFormed
public import Veir.IR.Grind

public section

namespace Veir

set_option quotPrecheck false

/-- The structural block obligations, allowing the designated block's arguments
    to be partially initialized. This notation introduces no new logical definition. -/
scoped notation "BlockPtrConstructionWellFormed" => fun (ctx : IRContext _) (building block : BlockPtr) (hb : block.InBounds ctx) =>
  Block.FieldsInBounds block ctx hb ∧
  (∀ i, i < block.getNumArguments! ctx → ((block.getArgument i).get! ctx).index = i) ∧
  (∀ i, i < block.getNumArguments! ctx → ((block.getArgument i).get! ctx).owner = block) ∧
  ((block.get! ctx).parent = none → (block.get! ctx).prev = none) ∧
  ((block.get! ctx).parent = none → (block.get! ctx).next = none) ∧
  (block ≠ building → (block.get! ctx).capArguments = block.getNumArguments! ctx)

/-- Context construction obligations. The two missing-use sets have the same meaning
    as in `IRContext.WellFormed`. All unaffected obligations are retained verbatim. -/
scoped notation "BlockConstructionWellFormed" => fun (ctx : IRContext _) (building : BlockPtr)
    (missingOperandUses : Std.ExtHashSet OpOperandPtr)
    (missingSuccessorUses : Std.ExtHashSet BlockOperandPtr) =>
  ctx.FieldsInBounds ∧
  (∀ valuePtr : ValuePtr, valuePtr.InBounds ctx →
    ∃ array, ValuePtr.DefUse valuePtr ctx array (missingOperandUses.filter (fun use => (use.get! ctx).value = valuePtr))) ∧
  (∀ blockPtr : BlockPtr, blockPtr.InBounds ctx →
    ∃ array, BlockPtr.DefUse blockPtr ctx array (missingSuccessorUses.filter (fun use => (use.get! ctx).value = blockPtr))) ∧
  (∀ blockPtr : BlockPtr, blockPtr.InBounds ctx → ∃ array, BlockPtr.OpChain blockPtr ctx array) ∧
  (∀ regionPtr : RegionPtr, regionPtr.InBounds ctx → ∃ array, RegionPtr.BlockChain regionPtr ctx array) ∧
  (∀ opPtr : OperationPtr, ∀ h : opPtr.InBounds ctx, opPtr.WellFormed ctx h) ∧
  (∀ blockPtr : BlockPtr, ∀ h : blockPtr.InBounds ctx, BlockPtrConstructionWellFormed ctx building blockPtr h) ∧
  (∀ regionPtr : RegionPtr, regionPtr.InBounds ctx → regionPtr.WellFormed ctx)

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo} {building block : BlockPtr}
variable {missingOperandUses : Std.ExtHashSet OpOperandPtr}
variable {missingSuccessorUses : Std.ExtHashSet BlockOperandPtr}

namespace BlockPtr.BlockConstructionWellFormed

 theorem of_wellFormed (h : block.WellFormed ctx hb) :
    BlockPtrConstructionWellFormed ctx building block hb := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, fun _ => h₆⟩

 theorem to_wellFormed (h : BlockPtrConstructionWellFormed ctx building block hb)
    (arguments : (block.get! ctx).capArguments = block.getNumArguments! ctx) :
    block.WellFormed ctx hb := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, _⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, arguments⟩

 theorem other_wellFormed (h : BlockPtrConstructionWellFormed ctx building block hb)
    (hne : block ≠ building) : block.WellFormed ctx hb :=
  to_wellFormed h (h.2.2.2.2.2 hne)

end BlockPtr.BlockConstructionWellFormed

namespace IRContext.BlockConstructionWellFormed

theorem inBounds (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses) :
    ctx.FieldsInBounds := h.1

 theorem valueDefUseChains (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (v : ValuePtr) (hv : v.InBounds ctx) :
    ∃ a, v.DefUse ctx a (missingOperandUses.filter (fun use => (use.get! ctx).value = v)) := h.2.1 v hv

 theorem blockDefUseChains (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (b : BlockPtr) (hb : b.InBounds ctx) :
    ∃ a, b.DefUse ctx a (missingSuccessorUses.filter (fun use => (use.get! ctx).value = b)) := h.2.2.1 b hb

 theorem opChain (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (b : BlockPtr) (hb : b.InBounds ctx) : ∃ a, b.OpChain ctx a := h.2.2.2.1 b hb

 theorem blockChain (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (r : RegionPtr) (hr : r.InBounds ctx) : ∃ a, r.BlockChain ctx a := h.2.2.2.2.1 r hr

 theorem operations (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (o : OperationPtr) (ho : o.InBounds ctx) : o.WellFormed ctx ho := h.2.2.2.2.2.1 o ho

 theorem blocks (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (b : BlockPtr) (hb : b.InBounds ctx) : BlockPtrConstructionWellFormed ctx building b hb := h.2.2.2.2.2.2.1 b hb

 theorem regions (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (r : RegionPtr) (hr : r.InBounds ctx) : r.WellFormed ctx := h.2.2.2.2.2.2.2 r hr

 theorem of_wellFormed (h : ctx.WellFormed missingOperandUses missingSuccessorUses) :
    BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses := by
  exact ⟨h.inBounds, h.valueDefUseChains, h.blockDefUseChains, h.opChain, h.blockChain,
    h.operations, fun _ hb => BlockPtr.BlockConstructionWellFormed.of_wellFormed (h.blocks _ hb), h.regions⟩

 theorem to_wellFormed (h : BlockConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (arguments : (building.get! ctx).capArguments = building.getNumArguments! ctx) :
    ctx.WellFormed missingOperandUses missingSuccessorUses := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.2⟩
  intro b hb
  by_cases heq : b = building
  · subst b
    exact BlockPtr.BlockConstructionWellFormed.to_wellFormed (blocks h building hb) arguments
  · exact BlockPtr.BlockConstructionWellFormed.other_wellFormed (blocks h b hb) heq

end IRContext.BlockConstructionWellFormed
end Veir
