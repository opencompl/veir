module

public import Veir.PatternRewriter.Puddle.CTreeGreedySoundness
public import Veir.PatternRewriter.DriverLemmas
public import Veir.PatternRewriter.CTreeDeadCode
import all Veir.PatternRewriter.CTreeDeadCode

public section
namespace Veir.Puddle.CTree

/-- Contexts obtainable from the input by successful greedy applications and safe
automatic erasures. Worklist order is irrelevant to this structural execution history. -/
inductive GreedyReachable (rules : Array (Veir.Puddle.Pattern OpCode))
    (initial : WfIRContext OpCode) : WfIRContext OpCode → Prop
  | initial : GreedyReachable rules initial initial
  | rewrite {before after : PatternRewriter OpCode} {op : OperationPtr}
      (opIn : op.InBounds before.ctx.raw)
      (prior : GreedyReachable rules initial before.ctx)
      (run : RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))
        before op opIn = some after) :
      GreedyReachable rules initial after.ctx
  | erase {ctx : WfIRContext OpCode} {op : OperationPtr}
      (opIn : op.InBounds ctx.raw) (dead : op.isTriviallyDead ctx.raw)
      (noAllocation : (op.getEffects ctx.raw).allocates = false)
      (prior : GreedyReachable rules initial ctx) :
      GreedyReachable rules initial (WfRewriter.eraseOp ctx op dead.1 dead.2.1 opIn)

/-- The single-step placement domain is required for matches in verified contexts obtained
during rewriting. Matched operations may be in unreachable CFG blocks. -/
def AdmissibleGreedyMatches (rules : Array (Veir.Puddle.Pattern OpCode))
    (initial : WfIRContext OpCode) (moduleOp : OperationPtr) : Prop :=
  ∀ ctx, GreedyReachable rules initial ctx → ctx.Verified moduleOp →
    ∀ rule ∈ rules, ∀ op, op.InBounds ctx.raw → ∀ assignment,
      rule.matcher.run ctx.raw op = some assignment → RootAdmissible ctx moduleOp op

private def DriverInvariant (rules : Array (Veir.Puddle.Pattern OpCode))
    (initial : WfIRContext OpCode) (moduleOp : OperationPtr) (ctx : WfIRContext OpCode) : Prop :=
  GreedyReachable rules initial ctx ∧ ctx.Verified moduleOp ∧
    moduleOp.getOpType! ctx.raw = .builtin .module ∧ moduleOp.getParent! ctx.raw = none

private theorem greedy_contextSteps
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    (erasure : VerifiedDeadCodeErasure)
    {initial : WfIRContext OpCode} {moduleOp : OperationPtr}
    (admissible : AdmissibleGreedyMatches rules initial moduleOp) :
    RewritePattern.ContextStepPreserves
      (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run)))
      (DriverInvariant rules initial moduleOp)
      (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after) := by
  constructor
  · intro before op opIn after prior run
    obtain ⟨refines, verified, code, noParent⟩ := valid_rules_greedy_moduleRefinement_of_matches rules valid
      opIn prior.2.2.1 prior.2.1 prior.2.2.2
      (fun rule member assignment matched => admissible before.ctx prior.1 prior.2.1
        rule member op opIn assignment matched) run
    exact ⟨⟨.rewrite opIn prior.1 run, verified, code, noParent⟩, refines⟩
  · intro before op opIn dead noAllocation prior
    obtain ⟨verified, refines⟩ := erasure prior.2.1 prior.2.2.1 prior.2.2.2 opIn dead noAllocation
    have header := triviallyDead_erase_module_header prior.2.1 prior.2.2.1 prior.2.2.2 opIn dead
    rw [PatternRewriter.eraseOp_ctx opIn dead]
    exact ⟨⟨.erase opIn dead noAllocation prior.1, verified, header⟩, refines⟩

/-- The actual repeated greedy driver preserves its original module. The only
semantic obligation beyond single-pattern soundness is automatic dead-code erasure. -/
theorem valid_rules_applyInContext_moduleRefinement_of_erasure
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp traversalRoot : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (admissible : AdmissibleGreedyMatches rules before moduleOp)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))).applyInContext
      before traversalRoot maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  have result := RewritePattern.applyInContext_preserves_of_contextSteps
    (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))) traversalRoot
    (DriverInvariant rules before moduleOp)
    (fun source target => moduleOp.isModuleRefinedByCTree source moduleOp target)
    (greedy_contextSteps rules valid erasure admissible)
    (fun ctx prior => OperationPtr.isModuleRefinedByCTree_refl prior.2.1 moduleOp)
    (fun _ _ _ first second => OperationPtr.isModuleRefinedByCTree_trans first second)
    (before := before) (after := after) ⟨.initial, verified, moduleCode, moduleNoParent⟩ maxRounds run
  exact ⟨result.2, result.1.2.1⟩

/-- The function-wise wrapper also composes the actual repeated greedy runs. -/
theorem valid_rules_applyToFunctions_moduleRefinement_of_erasure
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp traversalRoot : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (admissible : AdmissibleGreedyMatches rules before moduleOp)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))).applyToFunctions
      before traversalRoot maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  let greedy : RewritePattern OpCode :=
    RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))
  have result : DriverInvariant rules before moduleOp after ∧
      moduleOp.isModuleRefinedByCTree before moduleOp after := by
    apply RewritePattern.applyToFunctions_preserves_of_contextSteps
      (OpInfo := OpCode) greedy traversalRoot
      (DriverInvariant rules before moduleOp)
      (fun source target => moduleOp.isModuleRefinedByCTree source moduleOp target)
      (greedy_contextSteps rules valid erasure admissible)
      (fun ctx prior => OperationPtr.isModuleRefinedByCTree_refl prior.2.1 moduleOp)
      (fun _ _ _ first second => OperationPtr.isModuleRefinedByCTree_trans first second)
      (before := before) (after := after) ⟨.initial, verified, moduleCode, moduleNoParent⟩ maxRounds
    dsimp only [greedy]
    exact run
  exact ⟨result.2, result.1.2.1⟩

/-- An array of valid Puddle rules preserves the original module through every successful
run of the repeated greedy driver, including automatic dead-code elimination. The structural
placement premise applies to matches in contexts reachable during rewriting. -/
theorem valid_rules_applyInContext_moduleRefinement
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp traversalRoot : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (admissible : AdmissibleGreedyMatches rules before moduleOp)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))).applyInContext
      before traversalRoot maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  valid_rules_applyInContext_moduleRefinement_of_erasure rules valid verifiedDeadCodeErasure
    moduleCode verified moduleNoParent admissible maxRounds run

/-- The same guarantee for the driver that visits each nested function. -/
theorem valid_rules_applyToFunctions_moduleRefinement
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp traversalRoot : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (admissible : AdmissibleGreedyMatches rules before moduleOp)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))).applyToFunctions
      before traversalRoot maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  valid_rules_applyToFunctions_moduleRefinement_of_erasure rules valid verifiedDeadCodeErasure
    moduleCode verified moduleNoParent admissible maxRounds run

/-- List-facing form of repeated greedy soundness; compilation preserves list order. -/
theorem valid_list_applyInContext_moduleRefinement
    (rules : List (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp traversalRoot : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (admissible : AdmissibleGreedyMatches rules.toArray before moduleOp)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern
      (rules.toArray.map (fun rule => rule.compile.run))).applyInContext
      before traversalRoot maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  exact valid_rules_applyInContext_moduleRefinement rules.toArray
    (by simpa using valid) moduleCode verified moduleNoParent admissible maxRounds run

end Veir.Puddle.CTree
