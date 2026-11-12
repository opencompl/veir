module

public import Veir.PatternRewriter.Puddle.CheckedExecutionLemmas
public import Veir.PatternRewriter.FilteredDriverLemmas
public import Veir.PatternRewriter.CTreeDeadCode
public import Veir.PatternRewriter.GreedyLemmas
import all Veir.PatternRewriter.Puddle.CheckedExecution
import all Veir.PatternRewriter.Puddle.CTreeGreedySoundness
import all Veir.PatternRewriter.CTreeDeadCode
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Basic

/-!
# Pointwise validity of rewrite patterns

The Puddle driver theorems of `CTreeCheckedDriverSoundness` are stated for a greedy combination of
compiled Puddle rules. The passes combine their rules in other ways too: nested greedy combinators,
a rule chosen per operation from a registry, and local rewrites that build a rule from the matched
operation. `RewritePattern.PointwiseValid` is the property of a rewrite pattern that those driver
theorems actually use: at an admissible root of a verified module, a successful run refines the
module, keeps the module root verified, and leaves the context alone when it reports no action.
Compiled valid rules have it, it is closed under the greedy combinator and under per-operation
choice, and it is what the filtered drivers preserve.
-/

public section
namespace Veir

open Puddle.CTree in
/-- The facts about the module root that every driver soundness theorem carries along: the
context is verified at the root, which is a `builtin.module` without a parent. -/
structure Puddle.CTree.ModuleRoot (ctx : WfIRContext OpCode) (moduleOp : OperationPtr) : Prop where
  verified : ctx.Verified moduleOp
  code : moduleOp.getOpType! ctx.raw = .builtin .module
  noParent : moduleOp.getParent! ctx.raw = none

/-- At an admissible root of a verified module, a successful run of the pattern refines the
module, keeps the module root, and does not change the context when it reports no action. -/
def RewritePattern.PointwiseValid (pattern : RewritePattern OpCode) : Prop :=
  ∀ {moduleOp root : OperationPtr} {rewriter result : PatternRewriter OpCode}
    (rootIn : root.InBounds rewriter.ctx.raw),
    Puddle.CTree.ModuleRoot rewriter.ctx moduleOp →
    Puddle.CTree.RootAdmissible rewriter.ctx moduleOp root →
    pattern rewriter root rootIn = some result →
      moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx ∧
      Puddle.CTree.ModuleRoot result.ctx moduleOp ∧
      (result.hasDoneAction = false → result.ctx = rewriter.ctx)

namespace RewritePattern

open Puddle.CTree

/-- A compiled valid Puddle rule is pointwise valid. -/
theorem PointwiseValid.compile {rule : Puddle.Pattern OpCode} (valid : Pattern.Valid rule) :
    PointwiseValid rule.compile.run := by
  intro moduleOp root rewriter result rootIn hroot adm run
  have admissible : ∀ assignment, rule.matcher.run rewriter.ctx.raw root = some assignment →
      RootAdmissible rewriter.ctx moduleOp root := fun _ _ => adm
  obtain ⟨refines, verified, code, noParent⟩ := valid.compile_moduleRefinement_of_matches rootIn
    hroot.code hroot.verified hroot.noParent admissible run
  exact ⟨refines, ⟨verified, code, noParent⟩, fun noAction =>
    valid.compile_ctx_eq_of_no_action_of_matches rootIn hroot.verified admissible run noAction⟩

/-- The greedy combination of pointwise valid patterns is pointwise valid. -/
theorem PointwiseValid.greedy {patterns : Array (RewritePattern OpCode)}
    (valid : ∀ pattern ∈ patterns, PointwiseValid pattern) :
    PointwiseValid (GreedyRewritePattern patterns) := by
  intro moduleOp root rewriter result rootIn hroot adm run
  have member : ∀ pattern ∈ patterns, ∀ (attempt res : PatternRewriter OpCode)
      (attemptIn : root.InBounds attempt.ctx.raw), attempt.ctx = rewriter.ctx →
      pattern attempt root attemptIn = some res →
        moduleOp.isModuleRefinedByCTree attempt.ctx moduleOp res.ctx ∧ ModuleRoot res.ctx moduleOp ∧
        (res.hasDoneAction = false → res.ctx = attempt.ctx) := by
    intro pattern memberOf attempt res attemptIn same ran
    have hroot' : ModuleRoot attempt.ctx moduleOp := by rw [same]; exact hroot
    have adm' : RootAdmissible attempt.ctx moduleOp root := by rw [same]; exact adm
    exact valid pattern memberOf attemptIn hroot' adm' ran
  have noAction : ∀ pattern ∈ patterns, ∀ (attempt res : PatternRewriter OpCode)
      (attemptIn : root.InBounds attempt.ctx.raw), attempt.ctx = rewriter.ctx →
      pattern attempt root attemptIn = some res → res.hasDoneAction = false →
        res.ctx = attempt.ctx :=
    fun pattern memberOf attempt res attemptIn same ran =>
      (member pattern memberOf attempt res attemptIn same ran).2.2
  have related := greedy_context_relation patterns
    (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after ∧
      ModuleRoot after moduleOp)
    ⟨OperationPtr.isModuleRefinedByCTree_refl hroot.verified moduleOp, hroot⟩ noAction
    (fun pattern memberOf attempt res attemptIn same ran =>
      ⟨(member pattern memberOf attempt res attemptIn same ran).1,
        (member pattern memberOf attempt res attemptIn same ran).2.1⟩) run
  refine ⟨related.1, related.2, fun noAct => ?_⟩
  rcases greedy_success_origin patterns noAction run with
    unchanged | ⟨pattern, memberOf, attempt, same, attemptIn, ran⟩
  · exact unchanged
  · exact ((member pattern memberOf attempt result attemptIn same ran).2.2 noAct).trans same

/-- The empty greedy combination, whose driver runs only erase dead operations. -/
theorem PointwiseValid.empty : PointwiseValid (GreedyRewritePattern #[]) :=
  PointwiseValid.greedy (by simp)

/-- The greedy combination of compiled valid rules, as the Puddle passes build it. -/
theorem PointwiseValid.greedy_compiled {rules : Array (Puddle.Pattern OpCode)}
    (valid : ∀ rule ∈ rules, Pattern.Valid rule) :
    PointwiseValid (GreedyRewritePattern (rules.map (fun rule => rule.compile.run))) :=
  PointwiseValid.greedy fun _ memberOf => by
    obtain ⟨rule, ruleMember, rfl⟩ := Array.mem_map.mp memberOf
    exact PointwiseValid.compile (valid rule ruleMember)

/-- A pattern that chooses, from the context and the operation, which pattern to run. -/
def ofChoice (choose : WfIRContext OpCode → OperationPtr → RewritePattern OpCode) :
    RewritePattern OpCode :=
  fun rewriter op opIn => choose rewriter.ctx op rewriter op opIn

/-- Choosing among pointwise valid patterns is pointwise valid. -/
theorem PointwiseValid.ofChoice {choose : WfIRContext OpCode → OperationPtr → RewritePattern OpCode}
    (valid : ∀ ctx op, PointwiseValid (choose ctx op)) : PointwiseValid (ofChoice choose) :=
  fun rootIn hroot adm run => valid _ _ rootIn hroot adm run

/-- The pattern that matches nothing. -/
def noop : RewritePattern OpCode :=
  fun rewriter _ _ => some { rewriter with hasDoneAction := false }

theorem PointwiseValid.noop : PointwiseValid noop := by
  intro moduleOp root rewriter result rootIn hroot _ run
  cases run
  exact ⟨OperationPtr.isModuleRefinedByCTree_refl hroot.verified moduleOp, hroot, fun _ => rfl⟩

/-- A local rewrite that interprets the Puddle rule chosen from the context and the operation,
and matches nothing when no rule is chosen. -/
def _root_.Veir.LocalRewritePattern.ofRule
    (choose : WfIRContext OpCode → OperationPtr → Option (Puddle.Pattern OpCode)) :
    LocalRewritePattern OpCode :=
  fun ctx op =>
    match choose ctx op with
    | some rule => Puddle.Pattern.interpret rule ctx op
    | none => some (ctx, none)

/-- Interpreting a chosen rule is running its compilation. -/
theorem fromLocalRewrite_ofRule
    (choose : WfIRContext OpCode → OperationPtr → Option (Puddle.Pattern OpCode)) :
    fromLocalRewrite (LocalRewritePattern.ofRule choose) =
      ofChoice fun ctx op =>
        match choose ctx op with
        | some rule => rule.compile.run
        | none => noop := by
  funext rewriter op opIn
  simp only [ofChoice]
  cases chosen : choose rewriter.ctx op with
  | some rule =>
    show fromLocalRewrite (LocalRewritePattern.ofRule choose) rewriter op opIn =
      fromLocalRewrite (Puddle.Pattern.interpret rule) rewriter op opIn
    simp only [fromLocalRewrite, LocalRewritePattern.ofRule, chosen]
  | none =>
    show fromLocalRewrite (LocalRewritePattern.ofRule choose) rewriter op opIn = noop rewriter op opIn
    simp only [fromLocalRewrite, LocalRewritePattern.ofRule, noop, chosen]
    rfl

/-- Choosing a valid rule per operation is pointwise valid. -/
theorem PointwiseValid.ofRule
    {choose : WfIRContext OpCode → OperationPtr → Option (Puddle.Pattern OpCode)}
    (valid : ∀ ctx op rule, choose ctx op = some rule → Pattern.Valid rule) :
    PointwiseValid (fromLocalRewrite (LocalRewritePattern.ofRule choose)) := by
  rw [fromLocalRewrite_ofRule]
  refine PointwiseValid.ofChoice fun ctx op => ?_
  cases chosen : choose ctx op with
  | some rule => exact PointwiseValid.compile (valid ctx op rule chosen)
  | none => exact PointwiseValid.noop

/-! ## The filtered drivers -/

/-- A pointwise valid pattern satisfies the step obligations of the module-filtered drivers. -/
theorem PointwiseValid.contextStepsIf {pattern : RewritePattern OpCode}
    (valid : PointwiseValid pattern) (moduleOp : OperationPtr) :
    ContextStepPreservesIf pattern (Puddle.rootEligible moduleOp)
      (fun ctx => ModuleRoot ctx moduleOp)
      (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after) := by
  constructor
  · intro before op opIn after prior eligible run
    obtain ⟨refines, root, _⟩ := valid opIn prior (Puddle.rootEligible_sound eligible) run
    exact ⟨root, refines⟩
  · intro before op opIn dead noAllocation prior _eligible
    obtain ⟨verified, refines⟩ :=
      verifiedDeadCodeErasure prior.verified prior.code prior.noParent opIn dead noAllocation
    have header := triviallyDead_erase_module_header prior.verified prior.code prior.noParent opIn dead
    rw [PatternRewriter.eraseOp_ctx opIn dead]
    exact ⟨⟨verified, header.1, header.2⟩, refines⟩

/-- Repeated application of a pointwise valid pattern in the module refines the module and keeps
the module root. -/
theorem PointwiseValid.applyInContextIf_moduleRoot {pattern : RewritePattern OpCode}
    (valid : PointwiseValid pattern) {before after : WfIRContext OpCode}
    {moduleOp traversalRoot : OperationPtr} (root : ModuleRoot before moduleOp) (maxRounds : Nat)
    (run : pattern.applyInContextIf (Puddle.rootEligible moduleOp) before traversalRoot maxRounds =
      some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ ModuleRoot after moduleOp :=
  have result := applyInContextIf_preserves_of_contextSteps pattern traversalRoot
    (Puddle.rootEligible moduleOp) (fun ctx => ModuleRoot ctx moduleOp)
    (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after)
    (PointwiseValid.contextStepsIf valid moduleOp)
    (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.verified moduleOp)
    (fun _ _ _ first second => OperationPtr.isModuleRefinedByCTree_trans first second)
    root maxRounds run
  ⟨result.2, result.1⟩

/-- The function-wise driver, likewise. -/
theorem PointwiseValid.applyToFunctionsIf_moduleRoot {pattern : RewritePattern OpCode}
    (valid : PointwiseValid pattern) {before after : WfIRContext OpCode}
    {moduleOp traversalRoot : OperationPtr} (root : ModuleRoot before moduleOp) (maxRounds : Nat)
    (run : pattern.applyToFunctionsIf (Puddle.rootEligible moduleOp) before traversalRoot
      maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ ModuleRoot after moduleOp :=
  have result := applyToFunctionsIf_preserves_of_contextSteps pattern traversalRoot
    (Puddle.rootEligible moduleOp) (fun ctx => ModuleRoot ctx moduleOp)
    (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after)
    (PointwiseValid.contextStepsIf valid moduleOp)
    (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.verified moduleOp)
    (fun _ _ _ first second => OperationPtr.isModuleRefinedByCTree_trans first second)
    root maxRounds run
  ⟨result.2, result.1⟩

/-- The checked-driver theorem of `CTreeCheckedDriverSoundness` is a special case. -/
theorem valid_rules_applyInModule_moduleRefinement'
    (rules : Array (Puddle.Pattern OpCode)) (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none) (maxRounds : Nat)
    (run : Puddle.applyInModule rules before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  have result := PointwiseValid.applyInContextIf_moduleRoot (PointwiseValid.greedy_compiled valid)
    ⟨verified, moduleCode, moduleNoParent⟩ maxRounds run
  ⟨result.1, result.2.verified⟩

end RewritePattern
end Veir
end
