module

public import Veir.PatternRewriter.Puddle.CheckedExecutionLemmas
public import Veir.PatternRewriter.FilteredDriverLemmas
public import Veir.PatternRewriter.CTreeDeadCode
import all Veir.PatternRewriter.Puddle.CheckedExecution
import all Veir.PatternRewriter.Puddle.CTreeGreedySoundness
import all Veir.PatternRewriter.CTreeDeadCode
import all Veir.PatternRewriter.Puddle.Execution

public section
namespace Veir.Puddle.CTree

private def CheckedModuleInvariant (moduleOp : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  ctx.Verified moduleOp ∧ moduleOp.getOpType! ctx.raw = .builtin .module ∧
    moduleOp.getParent! ctx.raw = none

/-- Every dispatched root satisfies placement by the actual runtime check. No invariant
about future matcher successes or the contents of the worklist is assumed. -/
private theorem checked_contextSteps
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    (erasure : VerifiedDeadCodeErasure) (moduleOp : OperationPtr) :
    RewritePattern.ContextStepPreservesIf
      (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run)))
      (rootEligible moduleOp) (CheckedModuleInvariant moduleOp)
      (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after) := by
  constructor
  · intro before op opIn after prior eligible run
    obtain ⟨rooted, region, parent, ssa, regions⟩ := rootEligible_sound eligible
    obtain ⟨refines, verified, code, noParent⟩ := valid_rules_greedy_moduleRefinement rules valid
      opIn prior.2.1 prior.1 rooted parent ssa regions run
    exact ⟨⟨verified, code, noParent⟩, refines⟩
  · intro before op opIn dead noAllocation prior _eligible
    obtain ⟨verified, refines⟩ := erasure prior.1 prior.2.1 prior.2.2 opIn dead noAllocation
    have header := triviallyDead_erase_module_header prior.1 prior.2.1 prior.2.2 opIn dead
    rw [PatternRewriter.eraseOp_ctx opIn dead]
    exact ⟨⟨verified, header⟩, refines⟩

/-- Repeated checked greedy rewriting, parameterized by the dead-code-erasure contract. -/
theorem valid_rules_applyInModule_moduleRefinement_of_erasure
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : applyInModule rules before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  have result : CheckedModuleInvariant moduleOp after ∧
      moduleOp.isModuleRefinedByCTree before moduleOp after := by
    apply RewritePattern.applyInContextIf_preserves_of_contextSteps
      (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))) moduleOp
      (rootEligible moduleOp) (CheckedModuleInvariant moduleOp)
      (fun source target => moduleOp.isModuleRefinedByCTree source moduleOp target)
      (checked_contextSteps rules valid erasure moduleOp)
      (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.1 moduleOp)
      (fun _ _ _ first second => OperationPtr.isModuleRefinedByCTree_trans first second)
      (before := before) (after := after) ⟨verified, moduleCode, moduleNoParent⟩ maxRounds
    exact run
  exact ⟨result.2, result.1.1⟩

/-- Checked function-wise rewriting, parameterized by the dead-code-erasure contract. -/
theorem valid_rules_applyToFunctionsInModule_moduleRefinement_of_erasure
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : applyToFunctionsInModule rules before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  have result : CheckedModuleInvariant moduleOp after ∧
      moduleOp.isModuleRefinedByCTree before moduleOp after := by
    apply RewritePattern.applyToFunctionsIf_preserves_of_contextSteps
      (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))) moduleOp
      (rootEligible moduleOp) (CheckedModuleInvariant moduleOp)
      (fun source target => moduleOp.isModuleRefinedByCTree source moduleOp target)
      (checked_contextSteps rules valid erasure moduleOp)
      (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.1 moduleOp)
      (fun _ _ _ first second => OperationPtr.isModuleRefinedByCTree_trans first second)
      (before := before) (after := after) ⟨verified, moduleCode, moduleNoParent⟩ maxRounds
    exact run
  exact ⟨result.2, result.1.1⟩

/-- A successful run of the checked module driver preserves module refinement and
verification. Placement is checked at dispatch, rather than required from the caller. -/
theorem valid_rules_applyInModule_moduleRefinement
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : applyInModule rules before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  valid_rules_applyInModule_moduleRefinement_of_erasure rules valid verifiedDeadCodeErasure
    moduleCode verified moduleNoParent maxRounds run

/-- The function-wise checked driver has the same guarantee, without a placement premise. -/
theorem valid_rules_applyToFunctionsInModule_moduleRefinement
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : applyToFunctionsInModule rules before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  valid_rules_applyToFunctionsInModule_moduleRefinement_of_erasure rules valid verifiedDeadCodeErasure
    moduleCode verified moduleNoParent maxRounds run

/-- List-facing form of checked greedy module refinement. -/
theorem valid_list_applyInModule_moduleRefinement
    (rules : List (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : applyInModule rules.toArray before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  exact valid_rules_applyInModule_moduleRefinement rules.toArray (by simpa using valid)
    moduleCode verified moduleNoParent maxRounds run

end Veir.Puddle.CTree
