module

public import Veir.Rewriter.Basic
public import Veir.Rewriter.WellFormed.Construction
import all Veir.Rewriter.Basic
import Veir.Rewriter.GetSet
import Veir.Rewriter.LinkedList.WellFormed

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]

theorem BlockPtr.DefUse.pushBlockOperand_construction_self
    {ctx : IRContext OpInfo} {op : OperationPtr} {block : BlockPtr} {hop hblock}
    (h : block.DefUse ctx array) :
    block.DefUse (Rewriter.pushBlockOperand ctx op block hop hblock) array
      (Std.ExtHashSet.ofList [op.nextBlockOperand ctx]) := by
  constructor <;> grind [BlockPtr.DefUse]

theorem BlockPtr.DefUse.pushBlockOperand_construction_other
    {ctx : IRContext OpInfo} {op : OperationPtr} {block other : BlockPtr} {hop hblock}
    (h : other.DefUse ctx array) (hne : other ≠ block) :
    other.DefUse (Rewriter.pushBlockOperand ctx op block hop hblock) array := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind [BlockPtr.DefUse]

variable [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

theorem Rewriter.pushBlockOperandAt_blockDefUse
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {idx block hop hb hi hc}
    (hchains : ∀ b : BlockPtr, b.InBounds ctx.spec → ∃ a, b.DefUse ctx.spec a)
    (b : BlockPtr) (hb' : b.InBounds ctx.spec) :
    ∃ a, b.DefUse (Rewriter.pushBlockOperandAt op ctx idx block hop hb hi hc).spec a := by
  have ⟨a, ha⟩ := hchains b hb'
  have ⟨a', ha'⟩ := hchains block.spec (by grind)
  simp only [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
  by_cases he : b = block.spec
  · subst b
    refine ⟨_, Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_self_empty (array := a) (by grind) ?_⟩
    have hh := BlockPtr.DefUse.pushBlockOperand_construction_self (op := op.spec) (hop := hop.ib) (hblock := hb.ib) ha
    simpa [Rewriter.pushBlockOperandAtUnattached_spec, Sim.OperationPtr.getBlockOperandPtr_def,
      Sim.OperationPtr.getBlockOperandPtrSim, hi, OperationPtr.nextBlockOperand,
      OperationPtr.getBlockOperand, OperationPtr.getNumSuccessors!_eq_getNumSuccessors (hin := hop.ib)] using hh
  · refine ⟨a, Sim.BlockPtr.defUse_BlockOperandPtr_insertIntoCurrent_other
      (array' := a') (missingUses' := Std.ExtHashSet.ofList [op.spec.nextBlockOperand ctx.spec])
      (by grind) he (hvalue := by
        simp [Sim.OperationPtr.getBlockOperandPtr_def, Sim.OperationPtr.getBlockOperandPtrSim,
          hi, OperationPtr.nextBlockOperand, OperationPtr.getBlockOperand,
          OperationPtr.getNumSuccessors!_eq_getNumSuccessors (hin := hop.ib)]) ?_ ?_⟩
    · simpa [Rewriter.pushBlockOperandAtUnattached_spec] using
        BlockPtr.DefUse.pushBlockOperand_construction_other (op := op.spec) (hop := hop.ib) (hblock := hb.ib) ha he
    · simpa [Rewriter.pushBlockOperandAtUnattached_spec] using
        BlockPtr.DefUse.pushBlockOperand_construction_self (op := op.spec) (hop := hop.ib) (hblock := hb.ib) ha'

set_option maxHeartbeats 1200000 in
theorem Rewriter.pushBlockOperandAt_constructionWellFormed
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {idx block hop hb hi hc}
    (wf : ConstructionWellFormed ctx.spec op.spec ∅ ∅) :
    ConstructionWellFormed (Rewriter.pushBlockOperandAt op ctx idx block hop hb hi hc).spec op.spec ∅ ∅ := by
  have hin := wf.1
  refine ⟨by grind, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros v hv
    have ⟨a, ha⟩ := IRContext.ConstructionWellFormed.valueDefUseChains wf v (by grind)
    exists a
    simp only [pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
    apply Sim.ValuePtr.defUse_BlockOperandPtr_insertIntoCurrent
    apply ValuePtr.DefUse.unchanged (ctx := ctx.spec) <;> grind
  · intros b hb'
    simp only [Std.ExtHashSet.filter_empty]
    apply pushBlockOperandAt_blockDefUse
    · simpa using IRContext.ConstructionWellFormed.blockDefUseChains wf
    · grind
  · intros b hb'
    have ⟨a, ha⟩ := IRContext.ConstructionWellFormed.opChain wf b (by grind)
    exists a
    simp only [pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
    apply Sim.BlockPtr.opChain_BlockOperandPtr_insertIntoCurrent
    apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind
  · intros r hr
    have ⟨a, ha⟩ := IRContext.ConstructionWellFormed.blockChain wf r (by grind)
    exists a
    simp only [pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
    apply Sim.RegionPtr.blockChain_BlockOperandPtr_insertIntoCurrent
    apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind
  · intros o ho
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
      IRContext.ConstructionWellFormed.operations wf o (by grind)
    simp only [pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
    refine ⟨by grind, by grind, by grind, by grind, by grind, by grind, ?_,
      by grind, by grind, by grind, by grind, by grind⟩
    intro r hr
    simpa [pushBlockOperandAtUnattached_spec] using h₇ r (by grind)
  · intros b hb'
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := IRContext.ConstructionWellFormed.blocks wf b (by grind)
    simp only [pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
    constructor <;> grind
  · intros r hr
    have ⟨h₁, h₂⟩ := IRContext.ConstructionWellFormed.regions wf r (by grind)
    simp only [pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]
    constructor
    · grind
    · intro parent hp
      have ⟨i, hi⟩ := h₂ (op := parent) (by simpa [pushBlockOperandAtUnattached_spec] using hp)
      exists i
      simpa [pushBlockOperandAtUnattached_spec] using hi

theorem Rewriter.initBlockOperands_constructionWellFormed
    {ctx ctx' : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄}
    (wf : ConstructionWellFormed ctx.spec op.spec ∅ ∅)
    (heq : Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄ = ctx') :
    ConstructionWellFormed ctx'.spec op.spec ∅ ∅ := by
  simp only [initBlockOperands_def] at heq
  fun_induction initBlockOperandsSim
  case case1 => subst ctx'; exact wf
  case case2 ctx0 index0 hop hoperands hidx hcap h value nextCtx ih =>
    apply ih _ heq
    exact pushBlockOperandAt_constructionWellFormed wf

@[grind .]
theorem Rewriter.initBlockOperands_numSuccessors
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄}
    (hindex : index.toNat ≤ operands.size) :
    op.spec.getNumSuccessors! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec = operands.size := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_numResults (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    ptr.getNumResults! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec = ptr.getNumResults! ctx.spec := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_numRegions (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    ptr.getNumRegions! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec = ptr.getNumRegions! ctx.spec := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_numOperands (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    ptr.getNumOperands! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec = ptr.getNumOperands! ctx.spec := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_capResults (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    (ptr.get! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec).capResults = (ptr.get! ctx.spec).capResults := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_capRegions (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    (ptr.get! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec).capRegions = (ptr.get! ctx.spec).capRegions := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_capOperands (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    (ptr.get! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec).capOperands = (ptr.get! ctx.spec).capOperands := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_capBlockOperands (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    (ptr.get! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec).capBlockOperands = (ptr.get! ctx.spec).capBlockOperands := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

@[grind .]
theorem Rewriter.initBlockOperands_preserves_parent (ptr : OperationPtr)
    {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr} {operands index h₁ h₂ h₃ h₄} :
    (ptr.get! (Rewriter.initBlockOperands op ctx operands index h₁ h₂ h₃ h₄).spec).parent = (ptr.get! ctx.spec).parent := by
  simp only [initBlockOperands_def]
  fun_induction initBlockOperandsSim <;>
    grind (gen := 20) [Rewriter.pushBlockOperandAt_def, Rewriter.pushBlockOperandAtSim]

end Veir
