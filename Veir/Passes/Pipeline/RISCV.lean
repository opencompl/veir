module

public import Veir.Passes.Pipeline.Soundness
public import Veir.Passes.DCE.Validity
public import Veir.Passes.CastsReconciliation.Validity
public import Veir.Passes.InstructionSelection.Branches.Pass
public import Veir.Passes.RISCVCombines.Validity.Strict
public import Veir.Passes.LLVMToGMIR.Soundness
public import Veir.Passes.Legalization.Validity
public import Veir.Passes.InstructionSelection.Proofs.RISCV64.Strict

/-!
# Correctness of the strict RISC-V pipeline

`riscvPipelineStrict` is the `riscv` pass group of `veir-opt`, each pass in its strict mode: a pure
function that checks its input and only runs rewrites proved to refine the module. The passes
whose strict mode is not yet written are parameters, and their soundness is a hypothesis of
`riscvPipelineStrict_sound`; each one that lands removes its hypothesis.
-/

public section
namespace Veir

/-- The `riscv` pipeline in strict mode. The passes still to be made strict are parameters. -/
def riscvPipelineStrict (callLowering legalize : PurePass) : List PurePass :=
  [LLVMToGMIRPass.runStrict, callLowering, PreLegalizerCombinerRISCV64Pass.runStrict, legalize,
   PostLegalizerCombinerRISCV64Pass.runStrict, ISelBrPass.runVerified true, ISelPass.runStrict,
   CastReconcilePass.runStrict, RISCV.Combine.runStrict, DCEPass.runStrict]

/-- A successful strict run of the RISC-V pipeline refines the module and leaves it verified,
provided the passes not yet made strict are sound. -/
theorem riscvPipelineStrict_sound {callLowering legalize : PurePass}
    (hCallLowering : callLowering.Sound) (hLegalize : legalize.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure (riscvPipelineStrict callLowering legalize) ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head (by
    simp only [List.forall_mem_cons]
    exact ⟨LLVMToGMIR.CTreeProofs.LLVMToGMIRPass.runStrict_sound, hCallLowering,
      Legalization.CTreeProofs.PreLegalizerCombinerRISCV64Pass.runStrict_sound, hLegalize,
      Legalization.CTreeProofs.PostLegalizerCombinerRISCV64Pass.runStrict_sound,
      ISelBrPass.runVerified_strict_sound, RISCV64Proofs.ISelPass.runStrict_sound,
      CastsReconciliation.CTreeProofs.CastReconcilePass.runStrict_sound,
      RISCV.CTreeProofs.Combine.runStrict_sound, DCEPass.runStrict_sound,
      fun _ member => nomatch member⟩) run

end Veir
end
