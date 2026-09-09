module

public import Veir.IR.WellFormed
public import Veir.IR.Grind

public section

namespace Veir

set_option quotPrecheck false

/-- The structural operation obligations, allowing the designated operation's arrays
    to be partially initialized. This notation introduces no new logical definition. -/
scoped notation "OperationConstructionWellFormed" => fun (ctx : IRContext _) (building op : OperationPtr) (hop : op.InBounds ctx) =>
  Operation.FieldsInBounds op ctx hop ∧
  (∀ i, i < op.getNumResults! ctx → ((op.getResult i).get! ctx).index = i) ∧
  (∀ i, i < op.getNumResults! ctx → ((op.getResult i).get! ctx).owner = op) ∧
  (∀ i, i < op.getNumOperands! ctx → ((op.getOpOperand i).get! ctx).owner = op) ∧
  (∀ i, i < op.getNumSuccessors! ctx → ((op.getBlockOperand i).get! ctx).owner = op) ∧
  (∀ i (hi : i < op.getNumRegions! ctx) j (hj : j < op.getNumRegions! ctx),
    i ≠ j → op.getRegion ctx i hop (by grind) ≠ op.getRegion ctx j hop (by grind)) ∧
  (∀ region : RegionPtr, region.InBounds ctx →
    ((∃ i, i < op.getNumRegions! ctx ∧ op.getRegion! ctx i = region) ↔
    (region.get! ctx).parent = some op)) ∧
  ((op.get! ctx).parent = none → (op.get! ctx).prev = none ∧ (op.get! ctx).next = none) ∧
  (op ≠ building → (op.get! ctx).capResults = op.getNumResults! ctx) ∧
  (op ≠ building → (op.get! ctx).capRegions = op.getNumRegions! ctx) ∧
  (op ≠ building → (op.get! ctx).capOperands = op.getNumOperands! ctx) ∧
  (op ≠ building → (op.get! ctx).capBlockOperands = op.getNumSuccessors! ctx)

/-- Context construction obligations. The two missing-use sets have the same meaning
    as in `IRContext.WellFormed`. All unaffected obligations are retained verbatim. -/
scoped notation "ConstructionWellFormed" => fun (ctx : IRContext _) (building : OperationPtr)
    (missingOperandUses : Std.ExtHashSet OpOperandPtr)
    (missingSuccessorUses : Std.ExtHashSet BlockOperandPtr) =>
  ctx.FieldsInBounds ∧
  (∀ valuePtr : ValuePtr, valuePtr.InBounds ctx →
    ∃ array, ValuePtr.DefUse valuePtr ctx array (missingOperandUses.filter (fun use => (use.get! ctx).value = valuePtr))) ∧
  (∀ blockPtr : BlockPtr, blockPtr.InBounds ctx →
    ∃ array, BlockPtr.DefUse blockPtr ctx array (missingSuccessorUses.filter (fun use => (use.get! ctx).value = blockPtr))) ∧
  (∀ blockPtr : BlockPtr, blockPtr.InBounds ctx → ∃ array, BlockPtr.OpChain blockPtr ctx array) ∧
  (∀ regionPtr : RegionPtr, regionPtr.InBounds ctx → ∃ array, RegionPtr.BlockChain regionPtr ctx array) ∧
  (∀ opPtr : OperationPtr, ∀ h : opPtr.InBounds ctx, OperationConstructionWellFormed ctx building opPtr h) ∧
  (∀ blockPtr : BlockPtr, ∀ h : blockPtr.InBounds ctx, blockPtr.WellFormed ctx h) ∧
  (∀ regionPtr : RegionPtr, regionPtr.InBounds ctx → regionPtr.WellFormed ctx)

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo} {building op : OperationPtr}
variable {missingOperandUses : Std.ExtHashSet OpOperandPtr}
variable {missingSuccessorUses : Std.ExtHashSet BlockOperandPtr}

namespace OperationPtr.ConstructionWellFormed

 theorem of_wellFormed (h : op.WellFormed ctx hop) :
    OperationConstructionWellFormed ctx building op hop := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, fun _ => h₉, fun _ => h₁₀, fun _ => h₁₁, fun _ => h₁₂⟩

 theorem to_wellFormed (h : OperationConstructionWellFormed ctx building op hop)
    (results : (op.get! ctx).capResults = op.getNumResults! ctx)
    (regions : (op.get! ctx).capRegions = op.getNumRegions! ctx)
    (operands : (op.get! ctx).capOperands = op.getNumOperands! ctx)
    (successors : (op.get! ctx).capBlockOperands = op.getNumSuccessors! ctx) :
    op.WellFormed ctx hop := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, _⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, results, regions, operands, successors⟩

 theorem other_wellFormed (h : OperationConstructionWellFormed ctx building op hop)
    (hne : op ≠ building) : op.WellFormed ctx hop := by
  exact to_wellFormed h (h.2.2.2.2.2.2.2.2.1 hne)
    (h.2.2.2.2.2.2.2.2.2.1 hne) (h.2.2.2.2.2.2.2.2.2.2.1 hne)
    (h.2.2.2.2.2.2.2.2.2.2.2 hne)

end OperationPtr.ConstructionWellFormed

namespace IRContext.ConstructionWellFormed

theorem inBounds (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses) :
    ctx.FieldsInBounds := h.1

 theorem valueDefUseChains (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (v : ValuePtr) (hv : v.InBounds ctx) :
    ∃ a, v.DefUse ctx a (missingOperandUses.filter (fun use => (use.get! ctx).value = v)) := h.2.1 v hv

 theorem blockDefUseChains (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (b : BlockPtr) (hb : b.InBounds ctx) :
    ∃ a, b.DefUse ctx a (missingSuccessorUses.filter (fun use => (use.get! ctx).value = b)) := h.2.2.1 b hb

 theorem opChain (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (b : BlockPtr) (hb : b.InBounds ctx) : ∃ a, b.OpChain ctx a := h.2.2.2.1 b hb

 theorem blockChain (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (r : RegionPtr) (hr : r.InBounds ctx) : ∃ a, r.BlockChain ctx a := h.2.2.2.2.1 r hr

 theorem operations (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (o : OperationPtr) (ho : o.InBounds ctx) : OperationConstructionWellFormed ctx building o ho := h.2.2.2.2.2.1 o ho

 theorem blocks (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (b : BlockPtr) (hb : b.InBounds ctx) : b.WellFormed ctx hb := h.2.2.2.2.2.2.1 b hb

 theorem regions (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (r : RegionPtr) (hr : r.InBounds ctx) : r.WellFormed ctx := h.2.2.2.2.2.2.2 r hr

 theorem of_wellFormed (h : ctx.WellFormed missingOperandUses missingSuccessorUses) :
    ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses := by
  exact ⟨h.inBounds, h.valueDefUseChains, h.blockDefUseChains, h.opChain, h.blockChain,
    fun _ ho => OperationPtr.ConstructionWellFormed.of_wellFormed (h.operations _ ho), h.blocks, h.regions⟩

 theorem to_wellFormed (h : ConstructionWellFormed ctx building missingOperandUses missingSuccessorUses)
    (results : (building.get! ctx).capResults = building.getNumResults! ctx)
    (regions : (building.get! ctx).capRegions = building.getNumRegions! ctx)
    (operands : (building.get! ctx).capOperands = building.getNumOperands! ctx)
    (successors : (building.get! ctx).capBlockOperands = building.getNumSuccessors! ctx) :
    ctx.WellFormed missingOperandUses missingSuccessorUses := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  intro o ho
  by_cases heq : o = building
  · subst o
    exact OperationPtr.ConstructionWellFormed.to_wellFormed (operations h building ho) results regions operands successors
  · exact OperationPtr.ConstructionWellFormed.other_wellFormed (operations h o ho) heq

end IRContext.ConstructionWellFormed
end Veir
