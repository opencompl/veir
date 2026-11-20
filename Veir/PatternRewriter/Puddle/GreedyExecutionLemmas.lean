module

public import Veir.PatternRewriter.Puddle.DriverScope
public import Veir.PatternRewriter.Puddle.ExecutionLemmas
import all Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Puddle.DriverStructure

namespace Veir.Puddle
public section
variable {OpInfo : Type} [HasOpInfo OpInfo]

theorem PatternRewriter.eraseOp_hasDoneAction (rewriter : PatternRewriter OpInfo) (op : OperationPtr)
    (regions unused inBounds) : (rewriter.eraseOp op regions unused inBounds).hasDoneAction = true := by
  simp [Veir.PatternRewriter.eraseOp]

theorem PatternRewriter.eraseOpBang_hasDoneAction (rewriter : PatternRewriter OpInfo) (op : OperationPtr)
    (inBounds : op.InBounds rewriter.ctx.raw) (regions : op.getNumRegions! rewriter.ctx.raw = 0)
    (unused : !op.hasUses! rewriter.ctx.raw) : (rewriter.eraseOp! op).hasDoneAction = true := by
  simp only [Veir.PatternRewriter.eraseOp!, dite_eq_left inBounds, dite_eq_left regions, dite_eq_left unused]
  exact eraseOp_hasDoneAction _ _ _ _ _

/-- Successful checked phase chains ensure that the final bang erasure sets the action marker. -/
theorem fromLocalRewrite_hasDoneAction_of_phases {pattern : LocalRewritePattern OpInfo}
    {rewriter result : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created inserted replaced : WfIRContext OpInfo}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some result)
    (insertions : InsertBeforeChain root newOps.toList created inserted)
    (substitutions : ReplaceResultChain root replacements.zipIdx.toList inserted replaced)
    (inBounds : root.InBounds replaced.raw) (regions : root.getNumRegions! replaced.raw = 0)
    (unused : !root.hasUses! replaced.raw) : result.hasDoneAction = true := by
  rw [fromLocalRewrite_eq_folds localRun run]
  apply PatternRewriter.eraseOpBang_hasDoneAction
  all_goals
    have contextEq :
        (replacements.zipIdx.foldl
          (fun (r : PatternRewriter OpInfo) pair => r.replaceValue! (root.getResult pair.2) pair.1)
          (newOps.foldl (fun (r : PatternRewriter OpInfo) op => r.insertOp! op (.before root))
            { rewriter with ctx := created, hasDoneAction := true })).ctx = replaced := by
      rw [← Array.foldl_hom (g₂ := fun (ctx : WfIRContext OpInfo) (pair : ValuePtr × Nat) =>
          WfRewriter.replaceValue! ctx (root.getResult pair.2) pair.1)
        (fun r : PatternRewriter OpInfo => r.ctx)
        (fun r pair => (PatternRewriter.replaceValueBang_ctx r (root.getResult pair.2) pair.1).symm)]
      rw [← Array.foldl_hom (g₂ := fun (ctx : WfIRContext OpInfo) (op : OperationPtr) =>
          WfRewriter.insertOp! ctx op (.before root))
        (fun r : PatternRewriter OpInfo => r.ctx)
        (fun r op => (PatternRewriter.insertOpBang_ctx r op (.before root)).symm)]
      have hi := insertions.eq_fold
      have hr := substitutions.eq_fold
      rw [Array.foldl_toList] at hi hr
      simpa only [hi] using hr
    simpa only [contextEq] using ‹_›

/-- Matching a structurally safe Puddle rewrite always sets the action marker. -/
theorem Pattern.compile_hasDoneAction_of_match (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : rule.compile.run rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (notOwn : ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
      (root.getResult index : ValuePtr) ≠ value) : result.hasDoneAction = true := by
  obtain ⟨inserted, replaced, hi, hr, hb, hregions, hu⟩ :=
    rule.fromLocalRewrite_safe_phases (rootIn := rootIn) localRun run attached regions notOwn
  exact fromLocalRewrite_hasDoneAction_of_phases (rootIn := rootIn) localRun run hi hr hb hregions hu

/-- A false marker means no matcher success, provided matched executions satisfy driver safety.
The final rewriter is exactly the original with its marker cleared. -/
theorem Pattern.compile_eq_of_no_action (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw}
    (run : rule.compile.run rewriter root rootIn = some result)
    (noAction : result.hasDoneAction = false)
    (safe : ∀ created newOps replacements,
      rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)) →
      (root.getParent! rewriter.ctx.raw).isSome = true ∧ root.getNumRegions! rewriter.ctx.raw = 0 ∧
      ∀ value ∈ replacements, ∀ index < root.getNumResults! rewriter.ctx.raw,
        (root.getResult index : ValuePtr) ≠ value) :
    result = { rewriter with hasDoneAction := false } := by
  cases matched : rule.matcher.run rewriter.ctx.raw root with
  | none =>
    have rejected := rule.compile_run_of_no_match rewriter root rootIn matched
    rw [rejected] at run
    exact Option.some.inj run.symm
  | some assignment =>
    cases created : rule.creation.run assignment rewriter.ctx with
    | none => simp [Pattern.compile, RewritePattern.fromLocalRewrite, Pattern.interpret, matched, created] at run
    | some output =>
      obtain ⟨ctx, ops, finalAssignment⟩ := output
      cases values : finalAssignment.getValues rule.replacement.values with
      | none => simp [Pattern.compile, RewritePattern.fromLocalRewrite, Pattern.interpret, matched, created, values] at run
      | some replacements =>
        have localRun : rule.interpret rewriter.ctx root = some (ctx, some (ops, replacements)) := by
          simp [Pattern.interpret, matched, created, values]
        obtain ⟨attached, regions, notOwn⟩ := safe ctx ops replacements localRun
        have action := rule.compile_hasDoneAction_of_match localRun run attached regions notOwn
        simp [noAction] at action


/-- The driver's runtime alias check supplies replacement safety even in unreachable blocks. -/
theorem Pattern.compile_eq_of_no_action_of_safe_root (rule : Pattern OpCode)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw}
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result)
    (noAction : result.hasDoneAction = false) :
    result = { rewriter with hasDoneAction := false } := by
  apply rule.compile_eq_of_no_action run noAction
  intro created ops replacements localRun
  exact ⟨attached, regions, fromLocalRewrite_result_notOwn_indexed (rootIn := rootIn) localRun run⟩

/-- Under the same source safety conditions as local soundness, no action is an exact
metadata-only return: the context and worklist are unchanged and the marker is cleared. -/
theorem CTree.Pattern.Valid.compile_eq_of_no_action {rule : Pattern OpCode}
    (valid : CTree.Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw}
    (ctxDom : rewriter.ctx.Dom irRoot) (rootRooted : root.RootedAt irRoot rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result)
    (noAction : result.hasDoneAction = false) :
    result = { rewriter with hasDoneAction := false } := by
  apply rule.compile_eq_of_no_action run noAction
  intro created ops replacements localRun
  exact ⟨attached, regions, (valid.replacement_contract_of_interpret ctxDom rootRooted rootRegion rootSSA
    rootReachable rootIn localRun).1⟩

/-- Worklist and action-marker metadata cannot affect the resulting context of two successful
compiled applications with the same input context and root. -/
theorem Pattern.compile_success_context_independent (rule : Pattern OpInfo)
    {left right leftResult rightResult : PatternRewriter OpInfo} {root : OperationPtr}
    {leftIn : root.InBounds left.ctx.raw} {rightIn : root.InBounds right.ctx.raw}
    (same : left.ctx = right.ctx)
    (leftRun : rule.compile.run left root leftIn = some leftResult)
    (rightRun : rule.compile.run right root rightIn = some rightResult) :
    leftResult.ctx = rightResult.ctx := by
  cases localResult : rule.interpret left.ctx root with
  | none => simp [Pattern.compile, RewritePattern.fromLocalRewrite, localResult] at leftRun
  | some output =>
    obtain ⟨created, rewrite⟩ := output
    have other : rule.interpret right.ctx root = some (created, rewrite) := by rw [← same]; exact localResult
    cases rewrite with
    | none =>
      simp only [Pattern.compile, RewritePattern.fromLocalRewrite, localResult] at leftRun
      simp only [Pattern.compile, RewritePattern.fromLocalRewrite, other] at rightRun
      cases leftRun
      cases rightRun
      rfl
    | some data =>
      obtain ⟨ops, replacements⟩ := data
      exact (fromLocalRewrite_ctx (rootIn := leftIn) localResult leftRun).trans
        (fromLocalRewrite_ctx (rootIn := rightIn) other rightRun).symm


/-- The bang driver's region-error arm returns the default rewriter, whose action marker is
false. This explains why no-action stability requires the checked phase safety hypotheses. -/
theorem fromLocalRewrite_empty_regions_fallback {pattern : LocalRewritePattern OpInfo}
    {rewriter : PatternRewriter OpInfo} {root : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (localRun : pattern rewriter.ctx root = some (rewriter.ctx, some (#[], #[])))
    (arity : root.getNumResults! rewriter.ctx.raw = 0)
    (regions : root.getNumRegions! rewriter.ctx.raw ≠ 0) :
    RewritePattern.fromLocalRewrite pattern rewriter root rootIn = some default := by
  simp [RewritePattern.fromLocalRewrite, localRun, arity, guard, Veir.PatternRewriter.eraseOp!,
    rootIn, regions]

end
end Veir.Puddle
