module

public import Veir.Passes.Pipeline.RISCVPure
import all Veir.Passes.Pipeline.RISCVPure
import all Veir.Passes.LLVMToGMIR
import all Veir.Passes.InstructionSelection.RISCV64Abi
import all Veir.Passes.GMIRCombines.RISCV64PreLegalizerCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.GMIRCombines.RISCV64PostLegalizerCombiner
import all Veir.Passes.InstructionSelection.RISCV64Branches
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.CastsReconciliation.Reconciliation
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.DCE.dce

/-!
# Correctness of the RISC-V pipeline

`riscvPipeline` is the `riscv` pass group of `veir-opt`, as the pass runner sees it.
`riscvPipeline_sound`: a successful untimed run of it, as `veir-opt` runs it, refines the module,
provided the call-lowering pass is a sound pure function. Each pass is the pure pass of
`riscvPipelinePure` (`Veir.Passes.Pipeline.RISCVPure`), which are all sound.
-/

public section
namespace Veir

/-- The `riscv` pass group of `veir-opt`, as the pass runner sees it: every pass under its default
options. -/
def riscvPipeline : PassPipeline OpCode :=
  ⟨#[(LLVMToGMIRPass, ∅), (CallLoweringRISCV64, ∅), (PreLegalizerCombinerRISCV64Pass, ∅),
     (LegalizeRISCV64Pass, ∅), (PostLegalizerCombinerRISCV64Pass, ∅), (IselBrRISCV64, ∅),
     (IselRISCV64, ∅), (CastReconcilePass, ∅), (RISCV.Combine, ∅), (DCEPass, ∅)]⟩

/-- A successful untimed run of the `riscv` pipeline by the pass runner refines the module and
leaves it verified, provided the call-lowering pass is a sound pure function. -/
theorem riscvPipeline_sound
    (hCallLowering : ∃ callLowering : PurePass,
      CallLoweringRISCV64.PureUnder ∅ callLowering ∧ callLowering.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (riscvPipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp := by
  obtain ⟨callLowering, pureUnder, sound⟩ := hCallLowering
  /- Each pass of `riscvPipeline` is the pure pass of `riscvPipelinePure`. -/
  have hPure : PassPipeline.PureList riscvPipeline.passes.toList
      (riscvPipelinePure callLowering) := by
    simp only [riscvPipeline, riscvPipelinePure, PassPipeline.PureList]
    refine ⟨fun _ _ _ => rfl, pureUnder, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
      ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, trivial⟩
    intro ctx op h
    show ISelBrPass.impl (((∅ : PassOptions).get? "strict").getD true) ctx op h = _
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty, Option.getD_none]
    exact ISelBrPass.impl_eq_runVerified true ctx op h
  exact PassPipeline.run_sound hPure (riscvPipelinePure_passes_sound sound) run


#print axioms riscvPipeline_sound

end Veir
end
