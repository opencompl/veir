module

public import Veir.PatternRewriter.CTreeStepCorrectness
public import Veir.PatternRewriter.Puddle.Internal.CheckedExecutionLemmas
public import Veir.PatternRewriter.Puddle.Internal.FilteredDriverLemmas
public import Veir.PatternRewriter.Puddle.Internal.CTreeDeadCode
import all Veir.PatternRewriter.Puddle.Internal.CheckedExecutionLemmas
import all Veir.PatternRewriter.Puddle.Internal.WorklistPointerScope
import all Veir.IR.OpCode
import all Veir.IRNesting
import all Veir.PatternRewriter.CTreeDeadCode
import all Veir.PatternRewriter.Puddle.Internal.CTreeGreedySoundness
import all Veir.PatternRewriter.Puddle.Internal.CTreeDeadCode
import all Veir.PatternRewriter.Puddle.Internal.DriverFunctionStructure
import all Veir.PatternRewriter.Puddle.Internal.DriverStructure
import all Veir.PatternRewriter.Basic
import all Veir.Rewriter.WfRewriter.Basic
import all Veir.PatternRewriter.Puddle.Execution

public section
namespace Veir.Puddle.CTree

private def CheckedModuleInvariant (moduleOp : OperationPtr) (initial ctx : WfIRContext OpCode) : Prop :=
  ctx.Verified moduleOp ∧ moduleOp.getOpType! ctx.raw = .builtin .module ∧
    moduleOp.getParent! ctx.raw = none ∧ ContainersPreserved moduleOp initial ctx

private theorem containers_refl (moduleOp : OperationPtr) (ctx : WfIRContext OpCode) :
    ContainersPreserved moduleOp ctx ctx := fun _ h n r => ⟨h, n, r⟩

private theorem compile_preserves_scope (rule : Veir.Puddle.Pattern OpCode)
    {before after : PatternRewriter OpCode} {op moduleOp : OperationPtr} {opIn}
    (verified : before.ctx.Verified moduleOp) (code : moduleOp.getOpType! before.ctx.raw = .builtin .module)
    (rooted : op.RootedAt moduleOp before.ctx)
    (all : before.worklist.All (CandidateInModule moduleOp before.ctx))
    (detached : moduleOp.getParent! after.ctx.raw = none)
    (attached : (op.getParent! before.ctx.raw).isSome) (regionless : op.getNumRegions! before.ctx.raw = 0)
    (run : rule.compile.run before op opIn = some after) :
    ContainersPreserved moduleOp before.ctx after.ctx ∧ after.worklist.All (CandidateInModule moduleOp after.ctx) := by
  change RewritePattern.fromLocalRewrite rule.interpret before op opIn = some after at run
  cases localRun : rule.interpret before.ctx op with
  | none => simp [RewritePattern.fromLocalRewrite, localRun] at run
  | some result =>
    obtain ⟨created, replacement⟩ := result
    cases replacement with
    | none =>
      have unchanged := rule.interpret_returnsCtxNoChanges before.ctx op created localRun
      simp only [RewritePattern.fromLocalRewrite, localRun] at run
      cases run
      exact unchanged ▸ ⟨containers_refl _ _, all⟩
    | some replacement =>
      exact rule.splice_preserves_scope localRun run attached regionless rooted detached verified code all

theorem compiled_correctStepInModule {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) : rule.compile.run.CorrectStepInModule := by
  constructor
  intro before after moduleOp op region opIn code verified rooted parent ssa regionless queued run
  obtain ⟨block, opParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp parent
  have attached : (op.getParent! before.ctx.raw).isSome := by simp [opParent]
  obtain ⟨code', detached⟩ := valid.compile_moduleHeader opIn code verified rooted parent ssa regionless run
  obtain ⟨containers, queued'⟩ := compile_preserves_scope rule verified code rooted queued detached
    attached regionless run
  exact ⟨valid.compile_moduleRefinement opIn code verified rooted parent ssa regionless run,
    valid.compile_preservesVerified opIn code verified rooted parent ssa attached regionless run,
    code', detached, containers, queued', fun flag => by
      rw [rule.compile_eq_of_no_action_of_safe_root attached regionless run flag]⟩

/-- Each greedy dispatch inherits the guarantees of the member that acts. -/
theorem greedy_correctStepInModule {rules : Array (RewritePattern OpCode)}
    (members : ∀ rule ∈ rules, rule.CorrectStepInModule) :
    (RewritePattern.GreedyRewritePattern rules).CorrectStepInModule := by
  constructor
  intro before after moduleOp op region opIn code verified rooted parent ssa regionless queued run
  let observe (r : PatternRewriter OpCode) := (r.ctx, r.worklist)
  have memberStep (pattern) (member : pattern ∈ rules) (attempt next : PatternRewriter OpCode)
      (attemptIn : op.InBounds attempt.ctx.raw) (same : observe attempt = observe before)
      (ran : pattern attempt op attemptIn = some next) :
      RewritePattern.ModuleStepResult moduleOp before.ctx before.worklist next := by
    obtain ⟨c, w⟩ := Prod.mk.inj same
    simpa only [c, w] using (members pattern member).step attemptIn (by simpa only [c] using code)
      (by simpa only [c] using verified) (by simpa only [c] using rooted)
      (by simpa only [c] using parent) (by simpa only [c] using ssa) (by simpa only [c] using regionless)
      (by simpa only [c, w] using queued) ran
  have origin := RewritePattern.greedy_success_origin_observe rules observe (fun _ _ => rfl)
    (fun pattern member attempt next bound same ran flag =>
      ((memberStep pattern member attempt next bound same ran).noAction flag).trans same.symm) run
  rcases origin with same | ⟨pattern, member, attempt, same, bound, ran⟩
  · obtain ⟨c, w⟩ := Prod.mk.inj same
    constructor
    · simpa only [c] using OperationPtr.isModuleRefinedByCTree_refl verified moduleOp
    · simpa only [c] using verified
    · simpa only [c] using code
    · simpa [c] using rooted.root_parent_eq
    · simpa only [ContainersPreserved, c] using containers_refl moduleOp before.ctx
    · simpa only [c, w] using queued
    · exact fun _ => same
  · exact memberStep pattern member attempt after bound same ran

private theorem checked_contextSteps {pattern : RewritePattern OpCode} (correct : pattern.CorrectStepInModule)
    (erasure : VerifiedDeadCodeErasure) (moduleOp : OperationPtr) (initial : WfIRContext OpCode) :
    RewritePattern.ScopedContextStepPreserves pattern
      (CandidateInModule moduleOp) (CheckedModuleInvariant moduleOp initial)
      (fun before after => moduleOp.isModuleRefinedByCTree before moduleOp after) := by
  constructor
  · intro before op opIn after prior queued candidate eligible run
    obtain ⟨rooted, region, parent, ssa, regionless⟩ := (rootEligible_iff (candidate opIn)).mp eligible
    have step := correct.step opIn prior.2.1 prior.1 rooted parent ssa regionless queued run
    exact ⟨⟨⟨step.verified, step.code, step.detached, prior.2.2.2.trans step.containers⟩, step.queued⟩, step.refines⟩
  · intro before op opIn dead noAllocation prior all candidate _
    obtain ⟨verified, code, noParent, containers⟩ := prior
    obtain ⟨verified', refines⟩ := erasure verified code noParent opIn dead noAllocation
    obtain ⟨code', detached⟩ := triviallyDead_erase_module_header verified code noParent opIn dead
    have queued := PatternRewriter.all_eraseOp before op dead.1 dead.2.1 opIn all (fun _ mem =>
      candidate_operand verified code noParent opIn (candidate opIn) mem)
    dsimp only
    rw [PatternRewriter.eraseOp_ctx opIn dead]
    have frame : ContainerFrame before.ctx (WfRewriter.eraseOp before.ctx op dead.1 dead.2.1 opIn) := by
      refine ⟨regionBlockHeadersPreserved_eraseOp, ?_⟩
      intro owner bound n
      have ne : owner ≠ op := by rintro rfl; have := dead.1; omega
      exact ⟨(Rewriter.eraseOp_inBounds (.operation owner) ne).mpr bound, operationHeaderPreserved_of_eraseOp ne bound⟩
    refine ⟨⟨⟨verified', code', detached, containers.trans (frame.containers detached)⟩, queued.mono ?_⟩, refines⟩
    intro p old h
    obtain ⟨ne, bound⟩ := eraseOp_survivor h
    exact frame.rooted detached bound (old bound) (operationHeaderPreserved_of_eraseOp ne bound).parent id

private theorem checked_round {pattern : RewritePattern OpCode} (correct : pattern.CorrectStepInModule)
    (erasure : VerifiedDeadCodeErasure) (moduleOp seed : OperationPtr) (initial : WfIRContext OpCode)
    (rooted : ∀ ctx, CheckedModuleInvariant moduleOp initial ctx → seed.RootedAt moduleOp ctx) :
    pattern.RoundPreserves seed
      (CheckedModuleInvariant moduleOp initial) (fun a b => moduleOp.isModuleRefinedByCTree a moduleOp b) :=
  RewritePattern.RoundPreserves.of_scopedContextSteps _ _ _ _ (CandidateInModule moduleOp)
    (fun ctx inv _ ancestry _ => ancestry.rootedAt_iff.mp (rooted ctx inv))
    (checked_contextSteps correct erasure moduleOp initial)
    (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.1 moduleOp)
    (fun _ _ _ => OperationPtr.isModuleRefinedByCTree_trans)

/-- Rewriting below any root in a verified builtin module refines the enclosing module. -/
theorem applyInContext_moduleRefinement_of_steps {pattern : RewritePattern OpCode} (correct : pattern.CorrectStepInModule)
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp root : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp) (rooted : root.RootedAt moduleOp before)
    (maxRounds : Nat)
    (run : pattern.applyInContext before root maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  by_cases container : root.InBounds before.raw ∧ 0 < root.getNumRegions! before.raw
  · have detached : moduleOp.getParent! before.raw = none := by simpa using rooted.root_parent_eq
    have result := RewritePattern.applyInContext_preserves _ root _ _
      (checked_round correct erasure moduleOp root before (fun _ prior =>
        (prior.2.2.2 root container.1 container.2 rooted).2.2))
      (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.1 moduleOp)
      (fun _ _ _ => OperationPtr.isModuleRefinedByCTree_trans)
      ⟨verified, moduleCode, detached, containers_refl _ _⟩ maxRounds run
    exact ⟨result.2, result.1.1⟩
  · obtain rfl := RewritePattern.applyInContext_eq_of_no_regions _ container run
    exact ⟨OperationPtr.isModuleRefinedByCTree_refl verified moduleOp, verified⟩

section

variable (rules : Array (RewritePattern OpCode))
    (valid : ∀ rule ∈ rules, ∃ puddleRule : Veir.Puddle.Pattern OpCode,
      rule = puddleRule.compile.run ∧ Pattern.Valid puddleRule)

include valid

/-- Each rewrite pattern in the array inherits the step guarantee of its compiled Puddle rule. -/
theorem valid_rules_correctSteps : ∀ rule ∈ rules, rule.CorrectStepInModule := by
  intro rule member
  obtain ⟨puddleRule, rfl, ruleValid⟩ := valid rule member
  exact compiled_correctStepInModule ruleValid

/-- Checked greedy rewriting parameterized by the dead-code-erasure contract. -/
theorem valid_rules_applyInModule_moduleRefinement_of_erasure
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp root : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp) (rooted : root.RootedAt moduleOp before)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern rules).applyInContext before root maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  applyInContext_moduleRefinement_of_steps (greedy_correctStepInModule (valid_rules_correctSteps rules valid))
    erasure moduleCode verified rooted maxRounds run

/-- Checked function-wise rewriting, parameterized by the dead-code-erasure contract. -/
theorem valid_rules_applyToFunctionsInModule_moduleRefinement_of_erasure
    (erasure : VerifiedDeadCodeErasure)
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern rules).applyToFunctions before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  have correct := greedy_correctStepInModule (valid_rules_correctSteps rules valid)
  have result := RewritePattern.applyToFunctions_preserves _ moduleOp
    (CheckedModuleInvariant moduleOp before) (fun a b => moduleOp.isModuleRefinedByCTree a moduleOp b)
    (fun f => checked_round correct erasure moduleOp f.val before (fun _ prior =>
      (prior.2.2.2 f.val f.property.1 f.property.2.1 ⟨f.property.2.2, by simp [moduleNoParent]⟩).2.2))
    (fun _ prior => OperationPtr.isModuleRefinedByCTree_refl prior.1 moduleOp)
    (fun _ _ _ => OperationPtr.isModuleRefinedByCTree_trans)
    ⟨verified, moduleCode, moduleNoParent, containers_refl _ _⟩ maxRounds run
  exact ⟨result.2, result.1.1⟩

/-- The function-wise checked driver has the same guarantee, without a placement premise. -/
theorem valid_rules_applyToFunctionsInModule_moduleRefinement
    {before after : WfIRContext OpCode} {moduleOp : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! before.raw = none)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern rules).applyToFunctions before moduleOp maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  valid_rules_applyToFunctionsInModule_moduleRefinement_of_erasure rules valid verifiedDeadCodeErasure
    moduleCode verified moduleNoParent maxRounds run

end

/-- List-facing form of checked greedy module refinement. -/
theorem valid_list_applyInModule_moduleRefinement
    (rules : List (RewritePattern OpCode))
    (valid : ∀ rule ∈ rules, ∃ puddleRule : Veir.Puddle.Pattern OpCode,
      rule = puddleRule.compile.run ∧ Pattern.Valid puddleRule)
    {before after : WfIRContext OpCode} {moduleOp root : OperationPtr}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp) (rooted : root.RootedAt moduleOp before)
    (maxRounds : Nat)
    (run : (RewritePattern.GreedyRewritePattern rules.toArray).applyInContext before root maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp := by
  exact valid_rules_applyInModule_moduleRefinement_of_erasure rules.toArray (by simpa using valid)
    verifiedDeadCodeErasure moduleCode verified rooted maxRounds run

end Veir.Puddle.CTree
