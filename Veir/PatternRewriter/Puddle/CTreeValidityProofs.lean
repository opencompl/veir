module

public import Veir.PatternRewriter.CTreeStepCorrectness
public import Veir.PatternRewriter.Puddle.CTreeValidity
public import Veir.PatternRewriter.Puddle.Execution
import Veir.PatternRewriter.Puddle.Internal.CTreeCheckedDriverSoundness

namespace Veir

/-- One successful application at an eligible operation refines the enclosing verified
module and preserves verification. Reporting no action leaves the IR context unchanged. -/
@[expose] public def RewritePattern.CorrectInModule (pattern : RewritePattern OpCode) : Prop :=
  ∀ {before after : PatternRewriter OpCode} {moduleOp op : OperationPtr} {region : RegionPtr}
    (bound : op.InBounds before.ctx.raw),
    moduleOp.getOpType! before.ctx.raw = .builtin .module → before.ctx.Verified moduleOp →
    op.RootedAt moduleOp before.ctx → op.getParentRegion! before.ctx.raw = some region →
    region.hasSSADominance before.ctx → op.getNumRegions! before.ctx.raw = 0 →
    pattern before op bound = some after →
    moduleOp.isModuleRefinedByCTree before.ctx moduleOp after.ctx ∧ after.ctx.Verified moduleOp ∧
      (after.hasDoneAction = false → after.ctx = before.ctx)

/-- Greedy choice preserves the per-visit guarantee, including for nested choices. -/
public theorem RewritePattern.GreedyRewritePattern_correctStep {rules : Array (RewritePattern OpCode)}
    (correct : ∀ rule ∈ rules, rule.CorrectStepInModule) :
    (RewritePattern.GreedyRewritePattern rules).CorrectStepInModule :=
  Puddle.CTree.greedy_correctStepInModule correct

/-- One application of greedy choice is correct whenever each member rewrite is correct. -/
public theorem RewritePattern.GreedyRewritePattern_correct {rules : Array (RewritePattern OpCode)}
    (correct : ∀ rule ∈ rules, rule.CorrectInModule) :
    (RewritePattern.GreedyRewritePattern rules).CorrectInModule := by
  intro before after moduleOp op region bound code verified rooted parent ssa regionless run
  have memberStep (rule) (mem : rule ∈ rules) (attempt result : PatternRewriter OpCode)
      (inside : op.InBounds attempt.ctx.raw) (same : attempt.ctx = before.ctx)
      (ran : rule attempt op inside = some result) := by
    rw [← same] at code verified rooted parent ssa regionless
    have step := correct rule mem inside code verified rooted parent ssa regionless ran
    rw [same] at step
    exact step
  rcases greedy_success_origin rules (fun rule mem attempt result inside same ran flag =>
    ((memberStep rule mem attempt result inside same ran).2.2 flag).trans same.symm) run with
    same | ⟨rule, mem, attempt, same, inside, ran⟩
  · rw [same]
    exact ⟨OperationPtr.isModuleRefinedByCTree_refl verified moduleOp, verified, fun _ => rfl⟩
  · exact memberStep rule mem attempt after inside same ran

/-- Running greedy choice across an entire worklist also requires each rewrite to preserve
the scope of subsequent visits. -/
public theorem RewritePattern.GreedyRewritePattern_applyInContext_moduleRefinement
    {rules : Array (RewritePattern OpCode)} (correct : ∀ rule ∈ rules, rule.CorrectStepInModule)
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp) (rooted : root.RootedAt moduleOp before)
    (run : (RewritePattern.GreedyRewritePattern rules).applyInContext before root maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  Puddle.CTree.applyInContext_moduleRefinement_of_steps (GreedyRewritePattern_correctStep correct)
    verifiedDeadCodeErasure moduleCode verified rooted maxRounds run

namespace Puddle.CTree

/-- A compiled valid Puddle rule can be used at any eligible greedy worklist visit. -/
public theorem Pattern.Valid.compile_correctStepInModule {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) : rule.compile.run.CorrectStepInModule :=
  compiled_correctStepInModule valid

/-- Applying one valid compiled Puddle rule refines the enclosing module. -/
public theorem Pattern.Valid.compile_correctInModule {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule) : rule.compile.run.CorrectInModule := by
  intro before after moduleOp op region bound code verified rooted parent ssa regionless run
  obtain ⟨block, opParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp parent
  have attached : (op.getParent! before.ctx.raw).isSome := by simp [opParent]
  exact ⟨valid.compile_moduleRefinement bound code verified rooted parent ssa regionless run,
    valid.compile_preservesVerified bound code verified rooted parent ssa attached regionless run,
    fun flag => by rw [rule.compile_eq_of_no_action_of_safe_root attached regionless run flag]⟩

/-- Running one valid compiled Puddle rule refines the enclosing module. -/
public theorem Pattern.Valid.applyInModule_moduleRefinement {rule : Veir.Puddle.Pattern OpCode}
    (valid : Pattern.Valid rule)
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp) (rooted : root.RootedAt moduleOp before)
    (run : rule.compile.run.applyInContext before root maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  applyInContext_moduleRefinement_of_steps valid.compile_correctStepInModule verifiedDeadCodeErasure
    moduleCode verified rooted maxRounds run

/-- Greedy rewriting with valid compiled Puddle rules refines the enclosing module. -/
public theorem valid_rules_applyInModule_moduleRefinement
    {rules : Array (RewritePattern OpCode)}
    (moduleCode : moduleOp.getOpType! before.raw = .builtin .module)
    (verified : before.Verified moduleOp) (rooted : root.RootedAt moduleOp before)
    (valid : ∀ rule ∈ rules, ∃ puddleRule : Veir.Puddle.Pattern OpCode,
      rule = puddleRule.compile.run ∧ Pattern.Valid puddleRule)
    (run : (RewritePattern.GreedyRewritePattern rules).applyInContext before root maxRounds = some after) :
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp :=
  RewritePattern.GreedyRewritePattern_applyInContext_moduleRefinement (rules := rules) (fun rule mem => by
    obtain ⟨puddleRule, rfl, h⟩ := valid rule mem
    exact h.compile_correctStepInModule) moduleCode verified rooted run

end Puddle.CTree
end Veir
