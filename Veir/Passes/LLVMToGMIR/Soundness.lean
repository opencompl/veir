module

public import Veir.Passes.LLVMToGMIR.Validity
public import Veir.Passes.LLVMToGMIR.BranchPass
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.LLVMToGMIR
import all Veir.Passes.LLVMToGMIR.Validity

/-! # Soundness of the `llvm-to-gmir` pass -/

public section
namespace Veir.LLVMToGMIR.CTreeProofs

open Puddle.CTree

/-- The pattern list of the pass is the list of patterns the certificate proves. -/
theorem llvmToGMIRPatternList_eq_provenPatterns :
    llvmToGMIRPatternList = llvmToGMIRCertificates.provenPatterns := by
  rfl

/-- Every pattern the pass applies is valid. -/
theorem llvmToGMIRPatternList_valid :
    ∀ rule ∈ llvmToGMIRPatternList, Pattern.Valid rule := by
  intro rule member
  rw [llvmToGMIRPatternList_eq_provenPatterns] at member
  exact llvmToGMIRCertificates.valid rule member

/-- The greedy combination of the patterns is pointwise valid. -/
theorem llvmToGMIRPatterns_pointwise :
    RewritePattern.PointwiseValid (RewritePattern.GreedyRewritePattern
      (llvmToGMIRPatternList.map fun rule => rule.compile.run).toArray) :=
  RewritePattern.PointwiseValid.greedy fun pattern member => by
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp member)
    exact RewritePattern.PointwiseValid.compile (llvmToGMIRPatternList_valid rule ruleMember)

/-- The `llvm-to-gmir` pass refines the module and leaves it verified: the branch step by its
own theorem, the patterns and the dead-code erasure by the checked drivers. -/
theorem LLVMToGMIRPass.run_sound : LLVMToGMIRPass.run.Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold LLVMToGMIRPass.run at run
  cases branches : LLVMToGMIRBranches.run true ctx moduleOp with
  | error message => simp [branches, Bind.bind, Except.bind] at run
  | ok translated =>
    rw [branches] at run
    simp only [Bind.bind, Except.bind] at run
    have refinesBranches := LLVMToGMIRBranches.run_strict_isModuleRefinedByCTree branches moduleOp
    cases checked : checkModuleRoot "llvm-to-gmir" translated moduleOp with
    | error message => simp [checked] at run
    | ok _ =>
      simp only [checked] at run
      cases patterns : applyToFunctionsChecked "llvm-to-gmir" (RewritePattern.GreedyRewritePattern
          (llvmToGMIRPatternList.map fun rule => rule.compile.run).toArray) translated
          moduleOp with
      | error message => simp [patterns] at run
      | ok lowered =>
        simp only [patterns] at run
        obtain ⟨refinesPatterns, rootLowered⟩ := applyToFunctionsChecked_moduleRoot
          llvmToGMIRPatterns_pointwise (ModuleRoot.of_checkModuleRoot checked) patterns
        obtain ⟨refinesErasure, root⟩ :=
          applyInContextChecked_moduleRoot RewritePattern.PointwiseValid.empty rootLowered run
        exact ⟨OperationPtr.isModuleRefinedByCTree_trans refinesBranches
          (OperationPtr.isModuleRefinedByCTree_trans refinesPatterns refinesErasure), root.verified⟩

/-- The pass with its IO returns what `LLVMToGMIRPass.run` does. -/
theorem LLVMToGMIRPass.impl_eq_run (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    LLVMToGMIRPass.impl ctx op opIn = ExceptT.mk (pure (LLVMToGMIRPass.run ctx op)) := by
  rw [LLVMToGMIRPass.impl]

end Veir.LLVMToGMIR.CTreeProofs
end
