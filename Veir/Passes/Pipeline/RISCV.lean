module

public import Veir.Passes.Pipeline.Soundness
public import Veir.Passes.DCE.Validity
public import Veir.Passes.CastsReconciliation.Validity
public import Veir.Passes.InstructionSelection.Branches.Pass
public import Veir.Passes.RISCVCombines.Validity.Pass
public import Veir.Passes.LLVMToGMIR.Soundness
public import Veir.Passes.Legalization.Validity
public import Veir.Passes.InstructionSelection.Proofs.RISCV64.Pass
public import Veir.Passes.Pipeline.Bridge
public import Veir.Passes.InstructionSelection.RISCV64Abi
import all Veir.Passes.LLVMToGMIR
import all Veir.Passes.InstructionSelection.RISCV64Abi
import all Veir.Passes.Legalization.RISCV64PreLegalizerCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.RISCV64PostLegalizerCombiner
import all Veir.Passes.InstructionSelection.RISCV64Branches
import all Veir.Passes.InstructionSelection.RISCV64
import all Veir.Passes.CastsReconciliation.Reconciliation
import all Veir.Passes.RISCVCombines.Combine
import all Veir.Passes.DCE.dce

/-!
# Correctness of the RISC-V pipeline

`riscvPipelinePure` is the `riscv` pass group of `veir-opt`, each pass as the pure function it
wraps: one that checks its input and only runs rewrites proved to refine the module. Call lowering
has no proof yet, so it is a parameter, and its soundness is a hypothesis of
`riscvPipelinePure_sound`. `riscvPipeline_sound` carries that to the pass runner: a successful
untimed run of the `riscv` pipeline, as `veir-opt` runs it, refines the module, provided the
call-lowering pass is a sound pure function.
-/

public section
namespace Veir

/-- The `riscv` pipeline as pure passes. Call lowering, not yet proved, is a parameter. -/
def riscvPipelinePure (callLowering : PurePass) : List PurePass :=
  [LLVMToGMIRPass.run, callLowering, PreLegalizerCombinerRISCV64Pass.run, LegalizeRISCV64Pass.run,
   PostLegalizerCombinerRISCV64Pass.run, ISelBrPass.runVerified true, ISelPass.run,
   CastReconcilePass.run, RISCV.Combine.run, DCEPass.run]

/-- Every pass of the pipeline is sound, provided call lowering is. -/
theorem riscvPipelinePure_passes_sound {callLowering : PurePass}
    (hCallLowering : callLowering.Sound) :
    ∀ pass ∈ riscvPipelinePure callLowering, pass.Sound := by
  simp only [riscvPipelinePure, List.forall_mem_cons]
  exact ⟨LLVMToGMIR.CTreeProofs.LLVMToGMIRPass.run_sound, hCallLowering,
    Legalization.CTreeProofs.PreLegalizerCombinerRISCV64Pass.run_sound,
    Legalization.CTreeProofs.LegalizeRISCV64Pass.run_sound,
    Legalization.CTreeProofs.PostLegalizerCombinerRISCV64Pass.run_sound,
    ISelBrPass.runVerified_strict_sound, RISCV64Proofs.ISelPass.run_sound,
    CastsReconciliation.CTreeProofs.CastReconcilePass.run_sound,
    RISCV.CTreeProofs.Combine.run_sound, DCEPass.run_sound,
    fun _ member => nomatch member⟩

/-- A successful run of the RISC-V pipeline refines the module and leaves it verified, provided
call lowering is sound. -/
theorem riscvPipelinePure_sound {callLowering : PurePass} (hCallLowering : callLowering.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure (riscvPipelinePure callLowering) ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head (riscvPipelinePure_passes_sound hCallLowering) run

/-! ## The pass runner -/

/-- The `riscv` pass group of `veir-opt`, as the pass runner sees it: every pass under its default
options. -/
def riscvPipeline : PassPipeline OpCode :=
  ⟨#[(LLVMToGMIRPass, ∅), (CallLoweringRISCV64, ∅), (PreLegalizerCombinerRISCV64Pass, ∅),
     (LegalizeRISCV64Pass, ∅), (PostLegalizerCombinerRISCV64Pass, ∅), (IselBrRISCV64, ∅),
     (IselRISCV64, ∅), (CastReconcilePass, ∅), (RISCV.Combine, ∅), (DCEPass, ∅)]⟩

/-- Each pass of `riscvPipeline` is the pure pass of `riscvPipelinePure`, given the pure core of
call lowering. -/
theorem riscvPipeline_pure {callLowering : PurePass}
    (hCallLowering : CallLoweringRISCV64.PureUnder ∅ callLowering) :
    PassPipeline.PureList riscvPipeline.passes.toList (riscvPipelinePure callLowering) := by
  simp only [riscvPipeline, riscvPipelinePure, PassPipeline.PureList]
  refine ⟨fun _ _ _ => rfl, hCallLowering, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    ?_, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, trivial⟩
  intro ctx op h
  show ISelBrPass.impl (((∅ : PassOptions).get? "strict").getD true) ctx op h = _
  simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty, Option.getD_none]
  exact ISelBrPass.impl_eq_runVerified true ctx op h

/-- A successful untimed run of the `riscv` pipeline by the pass runner refines the module and
leaves it verified, provided the call-lowering pass is a sound pure function. -/
theorem riscvPipeline_sound
    (hCallLowering : ∃ callLowering : PurePass,
      CallLoweringRISCV64.PureUnder ∅ callLowering ∧ callLowering.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (riscvPipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  let ⟨_, pureUnder, sound⟩ := hCallLowering
  PassPipeline.run_sound (riscvPipeline_pure pureUnder)
    (riscvPipelinePure_passes_sound sound) run

end Veir
end
