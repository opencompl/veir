module

public import Veir.Passes.Pipeline.Soundness
public import Veir.Passes.DCE.Validity
public import Veir.Passes.CastsReconciliation.Validity
public import Veir.Passes.InstructionSelection.Branches.Pass

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
def riscvPipelineStrict (llvmToGmir callLowering preLegalizerCombiner legalize
    postLegalizerCombiner isel riscvCombine : PurePass) : List PurePass :=
  [llvmToGmir, callLowering, preLegalizerCombiner, legalize, postLegalizerCombiner,
   ISelBrPass.runVerified true, isel, CastReconcilePass.runStrict, riscvCombine, DCEPass.runStrict]

/-- A successful strict run of the RISC-V pipeline refines the module and leaves it verified,
provided the passes not yet made strict are sound. -/
theorem riscvPipelineStrict_sound {llvmToGmir callLowering preLegalizerCombiner legalize
    postLegalizerCombiner isel riscvCombine : PurePass}
    (hLlvmToGmir : llvmToGmir.Sound) (hCallLowering : callLowering.Sound)
    (hPreLegalizerCombiner : preLegalizerCombiner.Sound) (hLegalize : legalize.Sound)
    (hPostLegalizerCombiner : postLegalizerCombiner.Sound) (hIsel : isel.Sound)
    (hRiscvCombine : riscvCombine.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure (riscvPipelineStrict llvmToGmir callLowering preLegalizerCombiner legalize
      postLegalizerCombiner isel riscvCombine) ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head (by
    simp only [List.forall_mem_cons]
    exact ⟨hLlvmToGmir, hCallLowering, hPreLegalizerCombiner, hLegalize, hPostLegalizerCombiner,
      ISelBrPass.runVerified_strict_sound, hIsel,
      CastsReconciliation.CTreeProofs.CastReconcilePass.runStrict_sound, hRiscvCombine,
      DCEPass.runStrict_sound, fun _ member => nomatch member⟩) run

end Veir
end
