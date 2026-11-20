module

public import Veir.Passes.Pipeline.Soundness
public import Veir.Passes.DCE.Validity
public import Veir.Passes.CastsReconciliation.Validity
public import Veir.Passes.InstructionSelection.Branches.Pass
public import Veir.Passes.RISCVCombines.Validity.Pass
public import Veir.Passes.LLVMToGMIR.Soundness
public import Veir.Passes.Legalization.Validity
public import Veir.Passes.GMIRCombines.Validity.Pass
public import Veir.Passes.InstructionSelection.Proofs.RISCV64.Pass
public import Veir.Passes.Pipeline.Bridge
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
# Soundness of the pure LLVM-to-RISC-V pipeline

The pipeline lowers LLVM to GMIR and then runs the RISC-V passes, omitting call lowering.
-/

public section
namespace Veir

def llvmToRISCVPipelinePure : List PurePass :=
  [LLVMToGMIRPass.run, PreLegalizerCombinerRISCV64Pass.run, LegalizeRISCV64Pass.run,
   PostLegalizerCombinerRISCV64Pass.run, ISelBrPass.runVerified true, ISelPass.run,
   CastReconcilePass.run, RISCV.Combine.run, DCEPass.run]

theorem llvmToRISCVPipelinePure_passes_sound :
    ∀ pass ∈ llvmToRISCVPipelinePure, pass.Sound := by
  simp only [llvmToRISCVPipelinePure, List.forall_mem_cons]
  exact ⟨LLVMToGMIR.CTreeProofs.LLVMToGMIRPass.run_sound,
    GMIRCombines.CTreeProofs.PreLegalizerCombinerRISCV64Pass.run_sound,
    Legalization.CTreeProofs.LegalizeRISCV64Pass.run_sound,
    GMIRCombines.CTreeProofs.PostLegalizerCombinerRISCV64Pass.run_sound,
    ISelBrPass.runVerified_strict_sound, RISCV64Proofs.ISelPass.run_sound,
    CastsReconciliation.CTreeProofs.CastReconcilePass.run_sound,
    RISCV.CTreeProofs.Combine.run_sound, DCEPass.run_sound,
    fun _ member => nomatch member⟩

theorem llvmToRISCVPipelinePure_sound {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure llvmToRISCVPipelinePure ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head llvmToRISCVPipelinePure_passes_sound run

end Veir
end
