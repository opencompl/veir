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
# Correctness of the LLVM-to-RISC-V pass pipeline

A successful untimed run with default pass options refines the input module and produces
a verified module. The pipeline omits the call-lowering pass used by `veir-opt`.
-/

public section
namespace Veir

def llvmToRISCVPipeline : PassPipeline OpCode :=
  ⟨#[(LLVMToGMIRPass, ∅), (PreLegalizerCombinerRISCV64Pass, ∅), (LegalizeRISCV64Pass, ∅),
     (PostLegalizerCombinerRISCV64Pass, ∅), (IselBrRISCV64, ∅), (IselRISCV64, ∅),
     (CastReconcilePass, ∅), (RISCV.Combine, ∅), (DCEPass, ∅)]⟩

theorem llvmToRISCVPipeline_sound
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (llvmToRISCVPipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  have hPure : PassPipeline.PureList llvmToRISCVPipeline.passes.toList llvmToRISCVPipelinePure := by
    simp only [llvmToRISCVPipeline, llvmToRISCVPipelinePure, PassPipeline.PureList]
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, ?_,
      fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, trivial⟩
    intro ctx op h
    show ISelBrPass.impl (((∅ : PassOptions).get? "strict").getD true) ctx op h = _
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty, Option.getD_none]
    exact ISelBrPass.impl_eq_runVerified true ctx op h
  exact PassPipeline.run_sound hPure llvmToRISCVPipelinePure_passes_sound run

#print axioms llvmToRISCVPipeline_sound

end Veir
end
