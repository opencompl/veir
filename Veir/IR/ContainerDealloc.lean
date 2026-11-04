module

public import Veir.IR.GetSet
public import Veir.IR.InBounds
public import Veir.IR.WellFormed
import all Veir.IR.Basic

@[expose] public section
namespace Veir
variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo}

/-- Remove a block from the specification. Callers must first unlink it and
remove its contents and uses. The buffered API also releases its byte range. -/
def BlockPtr.dealloc (ptr : BlockPtr) (ctx : IRContext OpInfo) : IRContext OpInfo :=
  { ctx with blocks := ctx.blocks.erase ptr }

/-- Remove a region from the specification after unlinking its parent and blocks. -/
def RegionPtr.dealloc (ptr : RegionPtr) (ctx : IRContext OpInfo) : IRContext OpInfo :=
  { ctx with regions := ctx.regions.erase ptr }

setup_grind_with_get_set_definitions
attribute [local grind] BlockPtr.dealloc RegionPtr.dealloc
attribute [local grind] OperationPtr.inBounds_def BlockPtr.inBounds_def RegionPtr.inBounds_def
attribute [local grind] OpOperandPtr.InBounds BlockOperandPtr.InBounds BlockArgumentPtr.InBounds

@[simp, grind =]
theorem OperationPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : OperationPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : OperationPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : BlockPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : BlockPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx ∧ q ≠ ptr := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : RegionPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : RegionPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : OpResultPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : OpResultPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : OpOperandPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : OpOperandPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : BlockOperandPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : BlockOperandPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_BlockPtr_dealloc {ptr : BlockPtr} {q : BlockArgumentPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.inBounds_BlockPtr_dealloc {ptr : BlockPtr} {q : BlockArgumentPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx ∧ q.block ≠ ptr := by
  grind

@[simp, grind =]
theorem OperationPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : OperationPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem OperationPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : OperationPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : BlockPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem BlockPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : BlockPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : RegionPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem RegionPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : RegionPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx ∧ q ≠ ptr := by
  grind

@[simp, grind =]
theorem OpResultPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : OpResultPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem OpResultPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : OpResultPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : OpOperandPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem OpOperandPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : OpOperandPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : BlockOperandPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem BlockOperandPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : BlockOperandPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.get!_RegionPtr_dealloc {ptr : RegionPtr} {q : BlockArgumentPtr}
    (h : q.InBounds (ptr.dealloc ctx)) :
    q.get! (ptr.dealloc ctx) = q.get! ctx := by
  grind

@[simp, grind =]
theorem BlockArgumentPtr.inBounds_RegionPtr_dealloc {ptr : RegionPtr} {q : BlockArgumentPtr} :
    q.InBounds (ptr.dealloc ctx) ↔ q.InBounds ctx := by
  grind


@[grind →]
theorem ValuePtr.inBounds_BlockPtr_dealloc_old {ptr : BlockPtr} {v : ValuePtr}
    (h : v.InBounds (ptr.dealloc ctx)) : v.InBounds ctx := by
  cases v <;> grind [ValuePtr.InBounds]

@[simp, grind =]
theorem ValuePtr.getFirstUse!_BlockPtr_dealloc {ptr : BlockPtr} {v : ValuePtr}
    (h : v.InBounds (ptr.dealloc ctx)) :
    v.getFirstUse! (ptr.dealloc ctx) = v.getFirstUse! ctx := by
  cases v <;> grind [ValuePtr.InBounds, ValuePtr.getFirstUse!]

/-- Once the detached container has no remaining references, erasing its map
entry preserves all structural and def-use invariants. -/
theorem IRContext.wellFormed_BlockPtr_dealloc {ptr : BlockPtr}
    (wf : ctx.WellFormed) (hparent : (ptr.get! ctx).parent = none)
    (fib : (ptr.dealloc ctx).FieldsInBounds) : (ptr.dealloc ctx).WellFormed := by
  constructor
  · exact fib
  · intro v hv
    have hold : v.InBounds ctx := by grind
    obtain ⟨a, ha⟩ := wf.valueDefUseChains v hold
    refine ⟨a, ?_⟩
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    apply ha.unchanged hv <;> grind
  · intro b hb
    obtain ⟨a, ha⟩ := wf.blockDefUseChains b (by grind)
    refine ⟨a, ?_⟩
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    apply ha.unchanged hb <;> grind
  · intro b hb
    obtain ⟨a, ha⟩ := wf.opChain b (by grind)
    refine ⟨a, ?_⟩
    apply BlockPtr.OpChain_unchanged ha hb <;> grind
  · intro r hr
    obtain ⟨a, ha⟩ := wf.blockChain r (by grind)
    refine ⟨a, ?_⟩
    apply RegionPtr.blockChain_unchanged ha hr <;> grind
  · intro op hop
    apply OperationPtr.WellFormed_unchanged (wf.operations op (by grind))
      (fib.operations_inBounds op hop) <;> grind
  · intro b hb
    apply BlockPtr.WellFormed_unchanged (wf.blocks b (by grind))
      (fib.blocks_inBounds b hb) <;> grind
  · intro r hr
    apply RegionPtr.WellFormed_unchanged (wf.regions r (by grind))
      (fib.regions_inBounds r hr) <;> grind

@[grind →]
theorem ValuePtr.inBounds_RegionPtr_dealloc_old {ptr : RegionPtr} {v : ValuePtr}
    (h : v.InBounds (ptr.dealloc ctx)) : v.InBounds ctx := by
  cases v <;> grind [ValuePtr.InBounds]

@[simp, grind =]
theorem ValuePtr.getFirstUse!_RegionPtr_dealloc {ptr : RegionPtr} {v : ValuePtr}
    (h : v.InBounds (ptr.dealloc ctx)) :
    v.getFirstUse! (ptr.dealloc ctx) = v.getFirstUse! ctx := by
  cases v <;> grind [ValuePtr.InBounds, ValuePtr.getFirstUse!]

/-- Once the detached container has no remaining references, erasing its map
entry preserves all structural and def-use invariants. -/
theorem IRContext.wellFormed_RegionPtr_dealloc {ptr : RegionPtr}
    (wf : ctx.WellFormed) (hparent : (ptr.get! ctx).parent = none)
    (fib : (ptr.dealloc ctx).FieldsInBounds) : (ptr.dealloc ctx).WellFormed := by
  constructor
  · exact fib
  · intro v hv
    have hold : v.InBounds ctx := by grind
    obtain ⟨a, ha⟩ := wf.valueDefUseChains v hold
    refine ⟨a, ?_⟩
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    apply ha.unchanged hv <;> grind
  · intro b hb
    obtain ⟨a, ha⟩ := wf.blockDefUseChains b (by grind)
    refine ⟨a, ?_⟩
    simp only [Std.ExtHashSet.filter_empty] at ha ⊢
    apply ha.unchanged hb <;> grind
  · intro b hb
    obtain ⟨a, ha⟩ := wf.opChain b (by grind)
    refine ⟨a, ?_⟩
    apply BlockPtr.OpChain_unchanged ha hb <;> grind
  · intro r hr
    obtain ⟨a, ha⟩ := wf.blockChain r (by grind)
    refine ⟨a, ?_⟩
    apply RegionPtr.blockChain_unchanged ha hr <;> grind
  · intro op hop
    apply OperationPtr.WellFormed_unchanged (wf.operations op (by grind))
      (fib.operations_inBounds op hop) <;> grind
  · intro b hb
    apply BlockPtr.WellFormed_unchanged (wf.blocks b (by grind))
      (fib.blocks_inBounds b hb) <;> grind
  · intro r hr
    apply RegionPtr.WellFormed_unchanged (wf.regions r (by grind))
      (fib.regions_inBounds r hr) <;> grind

end Veir
