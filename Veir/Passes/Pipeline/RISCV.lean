module

public import Veir.Passes.Pipeline.RISCVPure
import all Veir.Passes.Pipeline.RISCVPure
import all Veir.Passes.LLVMToGMIR
import all Veir.Passes.GMIRCombines.RISCV64PreLegalizerCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.GMIRCombines.RISCV64PostLegalizerCombiner
import all Veir.Passes.InstructionSelection.RISCV64Branches
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.CastsReconciliation.Reconciliation
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.DCE.dce

/-!
# Correctness of the LLVM-to-GMIR and GMIR-to-RISC-V pass pipelines

The pass runner executes each segment with default pass options. The soundness theorems
apply to successful untimed runs of either segment.
-/

public section
namespace Veir

def llvmToGMIRPipeline : PassPipeline OpCode :=
  ⟨#[(LLVMToGMIRPass, ∅)]⟩

def gmirToRISCVPipeline : PassPipeline OpCode :=
  ⟨#[(PreLegalizerCombinerRISCV64Pass, ∅), (LegalizeRISCV64Pass, ∅),
     (PostLegalizerCombinerRISCV64Pass, ∅), (IselBrRISCV64, ∅), (IselRISCV64, ∅),
     (CastReconcilePass, ∅), (RISCV.Combine, ∅), (DCEPass, ∅)]⟩

theorem llvmToGMIRPipeline_sound
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (llvmToGMIRPipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  have hPure : PassPipeline.PureList llvmToGMIRPipeline.passes.toList llvmToGMIRPipelinePure :=
    ⟨fun _ _ _ => rfl, trivial⟩
  exact PassPipeline.run_sound hPure llvmToGMIRPipelinePure_passes_sound run

theorem gmirToRISCVPipeline_sound
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (gmirToRISCVPipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  have hPure : PassPipeline.PureList gmirToRISCVPipeline.passes.toList gmirToRISCVPipelinePure := by
    simp only [gmirToRISCVPipeline, gmirToRISCVPipelinePure, PassPipeline.PureList]
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, trivial⟩
    intro ctx op h
    show ISelBrPass.impl (((∅ : PassOptions).get? "strict").getD true) ctx op h = _
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty, Option.getD_none]
    exact ISelBrPass.impl_eq_runVerified true ctx op h
  exact PassPipeline.run_sound hPure gmirToRISCVPipelinePure_passes_sound run

#print axioms llvmToGMIRPipeline_sound
#print axioms gmirToRISCVPipeline_sound

end Veir
end
