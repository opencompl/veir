module

public import Veir.Passes.Pipeline.Soundness
public import Veir.Passes.DCE.Validity
public import Veir.Passes.CastsReconciliation.Validity
public import Veir.Passes.InstructionSelection.Branches.Pass
public import Veir.Passes.RISCVCombines.Validity.Strict
public import Veir.Passes.LLVMToGMIR.Soundness
public import Veir.Passes.Legalization.Validity
public import Veir.Passes.InstructionSelection.Proofs.RISCV64.Strict
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
# Correctness of the strict RISC-V pipeline

`riscvPipelineStrict` is the `riscv-strict` pass group of `veir-opt`, each pass in its strict
mode: a pure function that checks its input and only runs rewrites proved to refine the module.
Call lowering has no proof yet, so it is a parameter, and its soundness is a hypothesis of
`riscvPipelineStrict_sound`. `riscvStrictPipeline_sound` carries that to the pass runner: a
successful untimed run of the `riscv-strict` pipeline, as `veir-opt` runs it, refines the module,
provided the call-lowering pass is a sound pure function.
-/

public section
namespace Veir

/-- The `riscv` pipeline in strict mode. The passes still to be made strict are parameters. -/
def riscvPipelineStrict (callLowering : PurePass) : List PurePass :=
  [LLVMToGMIRPass.runStrict, callLowering, PreLegalizerCombinerRISCV64Pass.runStrict,
   LegalizeRISCV64Pass.runStrict,
   PostLegalizerCombinerRISCV64Pass.runStrict, ISelBrPass.runVerified true, ISelPass.runStrict,
   CastReconcilePass.runStrict, RISCV.Combine.runStrict, DCEPass.runStrict]

/-- Every pass of the strict pipeline is sound, provided call lowering is. -/
theorem riscvPipelineStrict_passes_sound {callLowering : PurePass}
    (hCallLowering : callLowering.Sound) :
    ∀ pass ∈ riscvPipelineStrict callLowering, pass.Sound := by
  simp only [riscvPipelineStrict, List.forall_mem_cons]
  exact ⟨LLVMToGMIR.CTreeProofs.LLVMToGMIRPass.runStrict_sound, hCallLowering,
    Legalization.CTreeProofs.PreLegalizerCombinerRISCV64Pass.runStrict_sound,
    Legalization.CTreeProofs.LegalizeRISCV64Pass.runStrict_sound,
    Legalization.CTreeProofs.PostLegalizerCombinerRISCV64Pass.runStrict_sound,
    ISelBrPass.runVerified_strict_sound, RISCV64Proofs.ISelPass.runStrict_sound,
    CastsReconciliation.CTreeProofs.CastReconcilePass.runStrict_sound,
    RISCV.CTreeProofs.Combine.runStrict_sound, DCEPass.runStrict_sound,
    fun _ member => nomatch member⟩

/-- A successful strict run of the RISC-V pipeline refines the module and leaves it verified,
provided call lowering is sound. -/
theorem riscvPipelineStrict_sound {callLowering : PurePass} (hCallLowering : callLowering.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr}
    (run : runPure (riscvPipelineStrict callLowering) ctx moduleOp = .ok ctx') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  runPure_sound_of_head (riscvPipelineStrict_passes_sound hCallLowering) run

/-! ## The pass runner -/

/-- The options that select the strict mode of a pass. -/
def strictOptions : PassOptions := (∅ : PassOptions).insert "strict" true

theorem strictOptions_strict (default : Bool) :
    (strictOptions.get? "strict").getD default = true := by
  simp [strictOptions]

/-- The `riscv-strict` pass group of `veir-opt`, as the pass runner sees it. -/
def riscvStrictPipeline : PassPipeline OpCode :=
  ⟨#[(LLVMToGMIRPass, strictOptions), (CallLoweringRISCV64, ∅),
     (PreLegalizerCombinerRISCV64Pass, strictOptions), (LegalizeRISCV64Pass, strictOptions),
     (PostLegalizerCombinerRISCV64Pass, strictOptions), (IselBrRISCV64, strictOptions),
     (IselRISCV64, strictOptions), (CastReconcilePass, strictOptions),
     (RISCV.Combine, strictOptions), (DCEPass, strictOptions)]⟩

/-- Each pass of `riscvStrictPipeline`, under its options, is the pure pass of
`riscvPipelineStrict`, given the pure core of call lowering. -/
theorem riscvStrictPipeline_pure {callLowering : PurePass}
    (hCallLowering : CallLoweringRISCV64.PureUnder ∅ callLowering) :
    PassPipeline.PureList riscvStrictPipeline.passes.toList (riscvPipelineStrict callLowering) := by
  simp only [riscvStrictPipeline, riscvPipelineStrict, PassPipeline.PureList]
  refine ⟨?_, hCallLowering, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · intro ctx op h
    show LLVMToGMIRPass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact LLVMToGMIR.CTreeProofs.LLVMToGMIRPass.impl_eq_runStrict ctx op h
  · intro ctx op h
    show PreLegalizerCombinerRISCV64Pass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact Legalization.CTreeProofs.PreLegalizerCombinerRISCV64Pass.impl_eq_runStrict ctx op h
  · intro ctx op h
    show LegalizeRISCV64Pass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact Legalization.CTreeProofs.LegalizeRISCV64Pass.impl_eq_runStrict ctx op h
  · intro ctx op h
    show PostLegalizerCombinerRISCV64Pass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact Legalization.CTreeProofs.PostLegalizerCombinerRISCV64Pass.impl_eq_runStrict ctx op h
  · intro ctx op h
    show ISelBrPass.impl ((strictOptions.get? "strict").getD true) ctx op h = _
    rw [strictOptions_strict]
    exact ISelBrPass.impl_eq_runVerified true ctx op h
  · intro ctx op h
    show ISelPass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact RISCV64Proofs.ISelPass.impl_eq_runStrict ctx op h
  · intro ctx op h
    show CastReconcilePass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact CastsReconciliation.CTreeProofs.CastReconcilePass.impl_eq_runStrict ctx op h
  · intro ctx op h
    show RISCV.Combine.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact RISCV.CTreeProofs.Combine.impl_eq_runStrict ctx op h
  · intro ctx op h
    show DCEPass.impl ((strictOptions.get? "strict").getD false) ctx op h = _
    rw [strictOptions_strict]
    exact DCEPass.impl_eq_runStrict ctx op h

/-- A successful untimed run of the `riscv-strict` pipeline by the pass runner refines the module
and leaves it verified, provided the call-lowering pass is a sound pure function. -/
theorem riscvStrictPipeline_sound
    (hCallLowering : ∃ callLowering : PurePass,
      CallLoweringRISCV64.PureUnder ∅ callLowering ∧ callLowering.Sound)
    {ctx ctx' : WfIRContext OpCode} {moduleOp : OperationPtr} {disableVerifiers : Bool}
    {s s' : Void IO.RealWorld}
    (run : (riscvStrictPipeline.run ctx moduleOp disableVerifiers false).run s = .ok (.ok ctx') s') :
    moduleOp.isModuleRefinedByCTree ctx moduleOp ctx' ∧ ctx'.Verified moduleOp :=
  let ⟨_, pureUnder, sound⟩ := hCallLowering
  PassPipeline.run_sound (riscvStrictPipeline_pure pureUnder)
    (riscvPipelineStrict_passes_sound sound) run

end Veir
end
