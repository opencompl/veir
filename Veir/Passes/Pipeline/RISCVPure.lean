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
# Soundness of the pure LLVM-to-GMIR and GMIR-to-RISC-V pipelines

These pipelines cover the two segments of the `veir-opt` RISC-V pass group on either side of
call lowering. Each successful run refines the input module and produces a verified module.
-/

public section
namespace Veir

def llvmToGMIRPipelinePure : List PurePass :=
  [LLVMToGMIRPass.run]

def gmirToRISCVPipelinePure : List PurePass :=
  [PreLegalizerCombinerRISCV64Pass.run, LegalizeRISCV64Pass.run,
   PostLegalizerCombinerRISCV64Pass.run, ISelBrPass.runVerified true, ISelPass.run,
   CastReconcilePass.run, RISCV.Combine.run, DCEPass.run]

theorem llvmToGMIRPipelinePure_passes_sound :
    ∀ pass ∈ llvmToGMIRPipelinePure, pass.Sound := by
  intro pass member
  obtain rfl : pass = LLVMToGMIRPass.run := List.mem_singleton.mp member
  exact LLVMToGMIR.CTreeProofs.LLVMToGMIRPass.run_sound

theorem gmirToRISCVPipelinePure_passes_sound :
    ∀ pass ∈ gmirToRISCVPipelinePure, pass.Sound := by
  simp only [gmirToRISCVPipelinePure, List.forall_mem_cons]
  exact ⟨GMIRCombines.CTreeProofs.PreLegalizerCombinerRISCV64Pass.run_sound,
    Legalization.CTreeProofs.LegalizeRISCV64Pass.run_sound,
    GMIRCombines.CTreeProofs.PostLegalizerCombinerRISCV64Pass.run_sound,
    ISelBrPass.runVerified_strict_sound, RISCV64Proofs.ISelPass.run_sound,
    CastsReconciliation.CTreeProofs.CastReconcilePass.run_sound,
    RISCV.CTreeProofs.Combine.run_sound, DCEPass.run_sound,
    fun _ member => nomatch member⟩

theorem llvmToGMIRPipelinePure_sound {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure llvmToGMIRPipelinePure ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head llvmToGMIRPipelinePure_passes_sound run

theorem gmirToRISCVPipelinePure_sound {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure gmirToRISCVPipelinePure ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head gmirToRISCVPipelinePure_passes_sound run

end Veir
end
