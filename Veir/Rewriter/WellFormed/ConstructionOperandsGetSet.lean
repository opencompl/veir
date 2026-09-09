module

public import Veir.Rewriter.Basic
import all Veir.Rewriter.Basic
import Veir.Rewriter.GetSet

public section
namespace Veir

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

theorem Rewriter.initOpOperands.loop_preserves_capResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    (ptr.get! ctx'.spec).capResults = (ptr.get! ctx.spec).capResults := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim, Rewriter.pushOperand]

theorem Rewriter.initOpOperands_preserves_capResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    (ptr.get! ctx'.spec).capResults = (ptr.get! ctx.spec).capResults := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · subst ctx'; rfl
  · exact Rewriter.initOpOperands.loop_preserves_capResults ptr heq

theorem Rewriter.initOpOperands.loop_preserves_capRegions (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    (ptr.get! ctx'.spec).capRegions = (ptr.get! ctx.spec).capRegions := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim, Rewriter.pushOperand]

theorem Rewriter.initOpOperands_preserves_capRegions (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    (ptr.get! ctx'.spec).capRegions = (ptr.get! ctx.spec).capRegions := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · subst ctx'; rfl
  · exact Rewriter.initOpOperands.loop_preserves_capRegions ptr heq

theorem Rewriter.initOpOperands.loop_preserves_capOperands (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    (ptr.get! ctx'.spec).capOperands = (ptr.get! ctx.spec).capOperands := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim, Rewriter.pushOperand]

theorem Rewriter.initOpOperands_preserves_capOperands (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    (ptr.get! ctx'.spec).capOperands = (ptr.get! ctx.spec).capOperands := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · subst ctx'; rfl
  · exact Rewriter.initOpOperands.loop_preserves_capOperands ptr heq

theorem Rewriter.initOpOperands.loop_preserves_numResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    ptr.getNumResults! ctx'.spec = ptr.getNumResults! ctx.spec := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim, Rewriter.pushOperand]

theorem Rewriter.initOpOperands_preserves_numResults (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    ptr.getNumResults! ctx'.spec = ptr.getNumResults! ctx.spec := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · subst ctx'; rfl
  · exact Rewriter.initOpOperands.loop_preserves_numResults ptr heq

theorem Rewriter.initOpOperands.loop_preserves_numRegions (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    ptr.getNumRegions! ctx'.spec = ptr.getNumRegions! ctx.spec := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim, Rewriter.pushOperand]

theorem Rewriter.initOpOperands_preserves_numRegions (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    ptr.getNumRegions! ctx'.spec = ptr.getNumRegions! ctx.spec := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · subst ctx'; rfl
  · exact Rewriter.initOpOperands.loop_preserves_numRegions ptr heq

theorem Rewriter.initOpOperands.loop_preserves_parent (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx') :
    (ptr.get! ctx'.spec).parent = (ptr.get! ctx.spec).parent := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [Rewriter.pushOperandAt_def, Rewriter.pushOperandAtSim, Rewriter.pushOperand]

theorem Rewriter.initOpOperands_preserves_parent (ptr : Veir.OperationPtr)
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx') :
    (ptr.get! ctx'.spec).parent = (ptr.get! ctx.spec).parent := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · subst ctx'; rfl
  · exact Rewriter.initOpOperands.loop_preserves_parent ptr heq

theorem Rewriter.initOpOperands.loop_numOperands
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo}
    {h₁ operands h₂ off index hidx hcap hoff}
    (heq : initOpOperands.loop opPtr ctx h₁ operands h₂ off index hidx hcap hoff = ctx')
    (hindex : index.toNat ≤ operands.size) :
    opPtr.spec.getNumOperands! ctx'.spec = operands.size := by
  simp only [Rewriter.initOpOperands.loop_def] at heq
  fun_induction initOpOperands.loopSim <;>
    grind [UInt64.le_iff_toNat_le, UInt64.toNat_add, UInt64.toNat_mod_size]

theorem Rewriter.initOpOperands_numOperands
    {opPtr : Sim.OperationPtr} {ctx ctx' : Sim.IRContext OpInfo} {h₁ operands h₂ index hidx hcap}
    (heq : initOpOperands opPtr ctx h₁ operands h₂ index hidx hcap = ctx')
    (hindex : index.toNat ≤ operands.size) :
    opPtr.spec.getNumOperands! ctx'.spec = operands.size := by
  simp only [Rewriter.initOpOperands_def, Rewriter.initOpOperandsSim] at heq
  split at heq
  · grind [UInt64.le_iff_toNat_le]
  · exact Rewriter.initOpOperands.loop_numOperands heq hindex

end Veir
