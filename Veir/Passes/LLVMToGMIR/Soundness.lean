module

public import Veir.Passes.LLVMToGMIR.Validity
public import Veir.Passes.LLVMToGMIR.BranchPass
public import Veir.Passes.Pipeline.Soundness
import all Veir.Passes.LLVMToGMIR
import all Veir.Passes.LLVMToGMIR.Validity

/-! # Soundness of the strict `llvm-to-gmir` pass -/

public section
namespace Veir.LLVMToGMIR.CTreeProofs

open Puddle.CTree

/-- The strict pattern list is the list of patterns the certificate proves. -/
theorem llvmToGMIRStrictPatternList_eq_provenPatterns :
    llvmToGMIRStrictPatternList = llvmToGMIRCertificates.provenPatterns := by
  rfl

/-- Every pattern the strict pass applies is valid. -/
theorem llvmToGMIRStrictPatternList_valid :
    ∀ rule ∈ llvmToGMIRStrictPatternList, Pattern.Valid rule := by
  intro rule member
  rw [llvmToGMIRStrictPatternList_eq_provenPatterns] at member
  exact llvmToGMIRCertificates.valid rule member

/-- The greedy combination of the strict patterns is pointwise valid. -/
theorem llvmToGMIRStrictPatterns_pointwise :
    RewritePattern.PointwiseValid (RewritePattern.GreedyRewritePattern
      (llvmToGMIRStrictPatternList.map fun rule => rule.compile.run).toArray) :=
  RewritePattern.PointwiseValid.greedy fun pattern member => by
    obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp member)
    exact RewritePattern.PointwiseValid.compile (llvmToGMIRStrictPatternList_valid rule ruleMember)

/-- The strict `llvm-to-gmir` pass refines the module and leaves it verified: the branch step by
its own theorem, the patterns and the dead-code erasure by the strict drivers. -/
theorem LLVMToGMIRPass.runStrict_sound : LLVMToGMIRPass.runStrict.Sound := by
  unfold PurePass.Sound
  intro ctx ctx' moduleOp run
  unfold LLVMToGMIRPass.runStrict at run
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
      cases patterns : applyToFunctionsStrict "llvm-to-gmir" (RewritePattern.GreedyRewritePattern
          (llvmToGMIRStrictPatternList.map fun rule => rule.compile.run).toArray) translated
          moduleOp with
      | error message => simp [patterns] at run
      | ok lowered =>
        simp only [patterns] at run
        obtain ⟨refinesPatterns, rootLowered⟩ := applyToFunctionsStrict_moduleRoot
          llvmToGMIRStrictPatterns_pointwise (ModuleRoot.of_checkModuleRoot checked) patterns
        obtain ⟨refinesErasure, root⟩ :=
          applyInContextStrict_moduleRoot RewritePattern.PointwiseValid.empty rootLowered run
        exact ⟨OperationPtr.isModuleRefinedByCTree_trans refinesBranches
          (OperationPtr.isModuleRefinedByCTree_trans refinesPatterns refinesErasure), root.verified⟩

/-- The pass with its IO, in strict mode, returns what `LLVMToGMIRPass.runStrict` does. -/
theorem LLVMToGMIRPass.impl_eq_runStrict (ctx : WfIRContext OpCode) (op : OperationPtr)
    (opIn : op.InBounds ctx.raw) :
    LLVMToGMIRPass.impl true ctx op opIn = ExceptT.mk (pure (LLVMToGMIRPass.runStrict ctx op)) := by
  rw [LLVMToGMIRPass.impl]
  rfl

end Veir.LLVMToGMIR.CTreeProofs
end
