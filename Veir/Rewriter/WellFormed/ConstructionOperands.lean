module

public import Veir.Rewriter.Basic
public import Veir.IR.WellFormed
public import Veir.Rewriter.WellFormed.Construction
import all Veir.Rewriter.Basic
import Veir.Rewriter.GetSet
import Veir.Rewriter.LinkedList.WellFormed

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo]
variable {ctx : IRContext OpInfo} {op : OperationPtr} {value : ValuePtr}
variable {hop : op.InBounds ctx} {hvalue : value.InBounds ctx}

/-- Appending an operand introduces exactly one temporarily unattached use. -/
theorem ValuePtr.DefUse.pushOperand_self
    (h : value.DefUse ctx array) :
    value.DefUse (Rewriter.pushOperand ctx op value hop hvalue) array
      (Std.ExtHashSet.ofList [op.nextOperand ctx]) := by
  constructor <;> grind [ValuePtr.DefUse]

/-- The use chains of other values survive appending an unattached operand. -/
theorem ValuePtr.DefUse.pushOperand_other
    (h : other.DefUse ctx array) (hne : other ≠ value) :
    other.DefUse (Rewriter.pushOperand ctx op value hop hvalue) array := by
  apply ValuePtr.DefUse.unchanged (ctx := ctx) <;> grind [ValuePtr.DefUse]

/-- Appending a successor introduces exactly one temporarily unattached block use. -/
theorem BlockPtr.DefUse.pushBlockOperand_self
    {block : BlockPtr} {hblock : block.InBounds ctx}
    (h : block.DefUse ctx array) :
    block.DefUse (Rewriter.pushBlockOperand ctx op block hop hblock) array
      (Std.ExtHashSet.ofList [op.nextBlockOperand ctx]) := by
  constructor <;> grind [BlockPtr.DefUse]

/-- The use chains of other blocks survive appending an unattached successor. -/
theorem BlockPtr.DefUse.pushBlockOperand_other
    {block : BlockPtr} {hblock : block.InBounds ctx}
    (h : other.DefUse ctx array) (hne : other ≠ block) :
    other.DefUse (Rewriter.pushBlockOperand ctx op block hop hblock) array := by
  apply BlockPtr.DefUse.unchanged (ctx := ctx) <;> grind [BlockPtr.DefUse]

section Sim
variable [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
variable {ctx : Sim.IRContext OpInfo} {op : Sim.OperationPtr}

theorem Rewriter.pushOperandAt_valueDefUse
    {off idx value hop hv hi hc ho}
    (hchains : ∀ v : ValuePtr, v.InBounds ctx.spec → ∃ a, v.DefUse ctx.spec a)
    (v : ValuePtr) (hv' : v.InBounds ctx.spec) :
    ∃ a, v.DefUse (Rewriter.pushOperandAt op ctx off idx value hop hv hi hc ho).spec a := by
  have ⟨a, ha⟩ := hchains v hv'
  have ⟨b, hb⟩ := hchains value.spec (by grind)
  simp only [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  by_cases he : v = value.spec
  · subst v
    refine ⟨_, Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_self_empty (array := a) (by grind) ?_⟩
    have hh := ValuePtr.DefUse.pushOperand_self (op := op.spec) (hop := hop.ib) (hvalue := hv.ib) ha
    simp only [Sim.OperationPtr.getOperandPtrAt_def, Sim.OperationPtr.getOperandPtrAtSim, pushOperandAtUninserted_spec]
    have heq : op.spec.getOpOperand idx.toNat = op.spec.nextOperand ctx.spec := by grind [OperationPtr.getOpOperand, OperationPtr.nextOperand]
    rw [heq]
    exact hh
  · refine ⟨a, Sim.ValuePtr.defUse_OpOperandPtr_insertIntoCurrent_other (array' := b) (missingUses' := Std.ExtHashSet.ofList [op.spec.nextOperand ctx.spec]) (by grind) he ?_ ?_ ?_⟩
    · show _ ∈ Std.ExtHashSet.ofList [op.spec.nextOperand ctx.spec]
      simp only [Sim.OperationPtr.getOperandPtrAt_def, Sim.OperationPtr.getOperandPtrAtSim]
      grind [OperationPtr.getOpOperand, OperationPtr.nextOperand]
    · simpa using ValuePtr.DefUse.pushOperand_other (op := op.spec) (hop := hop.ib) (hvalue := hv.ib) ha he
    · simpa using ValuePtr.DefUse.pushOperand_self (op := op.spec) (hop := hop.ib) hb

set_option maxHeartbeats 1000000 in
theorem Rewriter.pushOperandAt_constructionWellFormed
    {off idx value hop hv hi hc ho}
    (wf : ConstructionWellFormed ctx.spec op.spec ∅ ∅) :
    ConstructionWellFormed (Rewriter.pushOperandAt op ctx off idx value hop hv hi hc ho).spec op.spec ∅ ∅ := by
  refine ⟨by grind, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp only [Std.ExtHashSet.filter_empty]
    apply pushOperandAt_valueDefUse
    · intro v hv
      simpa using IRContext.ConstructionWellFormed.valueDefUseChains wf v hv
    · grind
  all_goals simp only [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim]
  · intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.blockDefUseChains wf blockPtr (by grind)
    exists array
    apply Sim.BlockPtr.defUse_OpOperandPtr_insertIntoCurrent
    simp only [Rewriter.pushOperandAtUninserted_spec]
    apply BlockPtr.DefUse.unchanged (ctx := ctx.spec) <;> grind
  · intros blockPtr blockPtrInBounds
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.opChain wf blockPtr (by grind)
    exists array
    apply Sim.BlockPtr.opChain_OpOperandPtr_insertIntoCurrent
    simp only [Rewriter.pushOperandAtUninserted_spec]
    apply BlockPtr.OpChain_unchanged (ctx := ctx.spec) <;> grind
  · intros reg hreg
    have ⟨array, arrayWf⟩ := IRContext.ConstructionWellFormed.blockChain wf reg (by grind)
    exists array
    apply Sim.RegionPtr.blockChain_OpOperandPtr_insertIntoCurrent
    simp only [Rewriter.pushOperandAtUninserted_spec]
    apply RegionPtr.blockChain_unchanged (ctx := ctx.spec) <;> grind
  · intros opPtr' opPtrInBounds
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ :=
      IRContext.ConstructionWellFormed.operations wf opPtr' (by grind)
    refine ⟨by grind, by grind, by grind, ?_, by grind, by grind, ?_, by grind,
      by grind, by grind, by grind, by grind⟩
    · intro i hi
      simp only [Sim.OpOperandPtr.get!_OpOperandPtr_insertIntoCurrent]
      grind [OperationPtr.getOpOperand, OperationPtr.nextOperand]
    · intro r hr
      simpa using h₇ r (by grind)
  · intros bl hbl
    have ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := IRContext.ConstructionWellFormed.blocks wf bl (by grind)
    constructor <;> grind
  · intros reg hreg
    have ⟨h₁, h₂⟩ := IRContext.ConstructionWellFormed.regions wf reg (by grind)
    constructor
    · grind
    · intro parent hp
      have ⟨i, hi⟩ := h₂ (op := parent) (by simpa using hp)
      exists i
      simpa using hi

theorem Rewriter.initOpOperands.loop_constructionWellFormed
    {ctx' : Sim.IRContext OpInfo} {hop operands hv off index hi hc ho}
    (wf : ConstructionWellFormed ctx.spec op.spec ∅ ∅)
    (heq : initOpOperands.loop op ctx hop operands hv off index hi hc ho = ctx') :
    ConstructionWellFormed ctx'.spec op.spec ∅ ∅ := by
  simp only [initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim
  case case1 =>
    cases heq
    exact wf
  case case2 ctx0 hop0 hv0 index0 hi0 hc0 ho0 h value0 nextCtx ih =>
    apply ih _ heq
    exact pushOperandAt_constructionWellFormed wf

theorem Rewriter.initOpOperands_constructionWellFormed
    {ctx' : Sim.IRContext OpInfo} {hop operands hv index hi hc}
    (wf : ConstructionWellFormed ctx.spec op.spec ∅ ∅)
    (heq : initOpOperands op ctx hop operands hv index hi hc = ctx') :
    ConstructionWellFormed ctx'.spec op.spec ∅ ∅ := by
  simp only [initOpOperands_def, initOpOperandsSim] at heq
  split at heq
  · cases heq
    exact wf
  · exact initOpOperands.loop_constructionWellFormed wf heq

end Sim
end Veir
