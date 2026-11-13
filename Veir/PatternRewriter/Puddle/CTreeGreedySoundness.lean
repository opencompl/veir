module

public import Veir.PatternRewriter.Puddle.CTreeGlobalSoundness
public import Veir.PatternRewriter.Puddle.GreedyExecutionLemmas
public import Veir.PatternRewriter.GreedyLemmas
import all Veir.PatternRewriter.Puddle.Execution
import all Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Semantics
import all Veir.IR.Basic
import all Veir.IRNesting

namespace Veir.Puddle.CTree
public section

/-- Placement conditions needed only when a rule actually matches a visited operation. -/
def RootAdmissible (ctx : WfIRContext OpCode) (moduleOp root : OperationPtr) : Prop :=
  root.RootedAt moduleOp ctx ∧ ∃ region,
    root.getParentRegion! ctx.raw = some region ∧ region.hasSSADominance ctx ∧
    root.getNumRegions! ctx.raw = 0

/-- Successful compiled execution preserves the module's opcode and unattached root header. -/
theorem Pattern.Valid.compile_moduleHeader
    {rule : Veir.Puddle.Pattern OpCode} (_valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (_sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (_rootSSA : region.hasSSADominance rewriter.ctx)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.getOpType! result.ctx.raw = .builtin .module ∧ moduleOp.getParent! result.ctx.raw = none := by
  have moduleNoParent : moduleOp.getParent! rewriter.ctx.raw = none := by
    simpa only [IRNode.parent!_operation, Option.map_eq_none_iff] using rootRooted.2
  obtain ⟨block, rootParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp rootRegion
  have attached : (root.getParent! rewriter.ctx.raw).isSome = true := by simp [rootParent]
  have driverRun : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result := run
  cases localRun : rule.interpret rewriter.ctx root with
  | none => simp [RewritePattern.fromLocalRewrite, localRun] at driverRun
  | some output =>
    obtain ⟨created, replacement⟩ := output
    cases replacement with
    | none =>
      have context := rule.interpret_returnsCtxNoChanges rewriter.ctx root created localRun
      simp only [RewritePattern.fromLocalRewrite, localRun] at driverRun
      cases driverRun
      simpa only [← context] using And.intro moduleCode moduleNoParent
    | some replacement =>
      obtain ⟨newOps, replacements⟩ := replacement
      have moduleIn : moduleOp.InBounds rewriter.ctx.raw := by
        by_cases inside : moduleOp.InBounds rewriter.ctx.raw
        · exact inside
        · simp only [OperationPtr.getOpType!, OperationPtr.get!_of_not_inBounds inside] at moduleCode
          contradiction
      have different : moduleOp ≠ root := by
        intro equal
        subst root
        simp [moduleNoParent] at attached
      have notOwn := fromLocalRewrite_result_notOwn_indexed localRun driverRun
      have header := (rule.fromLocalRewrite_existing_frame localRun driverRun attached regions
        notOwn moduleOp moduleIn different).1
      exact ⟨header.opcode.trans moduleCode, header.parent.trans moduleNoParent⟩

/-- The actual greedy choice among valid Puddle rules preserves verified module refinement.
Only the winning rule changes the context; earlier failed matches change at most rewriter metadata. -/
theorem valid_rules_greedy_moduleRefinement
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootRegion : root.getParentRegion! rewriter.ctx.raw = some region)
    (rootSSA : region.hasSSADominance rewriter.ctx)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (run : RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run)) rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx ∧ result.ctx.Verified moduleOp ∧
      moduleOp.getOpType! result.ctx.raw = .builtin .module ∧ moduleOp.getParent! result.ctx.raw = none := by
  have moduleNoParent : moduleOp.getParent! rewriter.ctx.raw = none := by
    simpa only [IRNode.parent!_operation, Option.map_eq_none_iff] using rootRooted.2
  obtain ⟨block, rootParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp rootRegion
  have attached : (root.getParent! rewriter.ctx.raw).isSome = true := by simp [rootParent]
  let relation (before after : WfIRContext OpCode) : Prop :=
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp ∧
      moduleOp.getOpType! after.raw = .builtin .module ∧ moduleOp.getParent! after.raw = none
  apply RewritePattern.greedy_context_relation (rules.map (fun rule => rule.compile.run)) relation
    (before := rewriter) (after := result) (op := root) (inBounds := rootIn) ?_ ?_ ?_ run
  · exact ⟨OperationPtr.isModuleRefinedByCTree_refl sourceVerified moduleOp,
      sourceVerified, moduleCode, moduleNoParent⟩
  · intro pattern member attempt next attemptIn context ran noAction
    obtain ⟨rule, ruleMember, rfl⟩ := Array.mem_map.mp member
    have unchanged := rule.compile_eq_of_no_action_of_safe_root
      (by simpa only [context] using attached) (by simpa only [context] using regions) ran noAction
    simpa only using congrArg PatternRewriter.ctx unchanged
  · intro pattern member attempt next attemptIn context ran
    obtain ⟨rule, ruleMember, rfl⟩ := Array.mem_map.mp member
    have ruleValid := valid rule ruleMember
    have code : moduleOp.getOpType! attempt.ctx.raw = .builtin .module := by simpa only [context] using moduleCode
    have verified : attempt.ctx.Verified moduleOp := by simpa only [context] using sourceVerified
    have rooted : root.RootedAt moduleOp attempt.ctx := by simpa only [context] using rootRooted
    have parent : root.getParentRegion! attempt.ctx.raw = some region := by simpa only [context] using rootRegion
    have ssa : region.hasSSADominance attempt.ctx := by simpa only [context] using rootSSA
    have attached' : (root.getParent! attempt.ctx.raw).isSome = true := by simpa only [context] using attached
    have noRegions : root.getNumRegions! attempt.ctx.raw = 0 := by simpa only [context] using regions
    exact ⟨ruleValid.compile_moduleRefinement attemptIn code verified rooted parent ssa noRegions ran,
      ruleValid.compile_preservesVerified attemptIn code verified rooted parent ssa attached' noRegions ran,
      ruleValid.compile_moduleHeader attemptIn code verified rooted parent ssa noRegions ran⟩


/-- Matching-only placement assumptions suffice for a compiled rule, including no-match visits
to operations with regions such as function declarations. -/
theorem Pattern.Valid.compile_moduleRefinement_of_matches
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! rewriter.ctx.raw = none)
    (admissible : ∀ assignment, rule.matcher.run rewriter.ctx.raw root = some assignment →
      RootAdmissible rewriter.ctx moduleOp root)
    (run : rule.compile.run rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx ∧ result.ctx.Verified moduleOp ∧
      moduleOp.getOpType! result.ctx.raw = .builtin .module ∧ moduleOp.getParent! result.ctx.raw = none := by
  cases matched : rule.matcher.run rewriter.ctx.raw root with
  | none =>
    rw [rule.compile_run_of_no_match rewriter root rootIn matched] at run
    cases run
    exact ⟨OperationPtr.isModuleRefinedByCTree_refl sourceVerified moduleOp,
      sourceVerified, moduleCode, moduleNoParent⟩
  | some assignment =>
    obtain ⟨rooted, region, parent, ssa, regions⟩ := admissible assignment matched
    obtain ⟨block, rootParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp parent
    have attached : (root.getParent! rewriter.ctx.raw).isSome = true := by simp [rootParent]
    exact ⟨valid.compile_moduleRefinement rootIn moduleCode sourceVerified rooted parent ssa regions run,
      valid.compile_preservesVerified rootIn moduleCode sourceVerified rooted parent ssa attached regions run,
      valid.compile_moduleHeader rootIn moduleCode sourceVerified rooted parent ssa regions run⟩

theorem Pattern.Valid.compile_ctx_eq_of_no_action_of_matches
    {rule : Veir.Puddle.Pattern OpCode} (_valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw) (_sourceVerified : rewriter.ctx.Verified moduleOp)
    (admissible : ∀ assignment, rule.matcher.run rewriter.ctx.raw root = some assignment →
      RootAdmissible rewriter.ctx moduleOp root)
    (run : rule.compile.run rewriter root rootIn = some result)
    (noAction : result.hasDoneAction = false) : result.ctx = rewriter.ctx := by
  cases matched : rule.matcher.run rewriter.ctx.raw root with
  | none =>
    rw [rule.compile_run_of_no_match rewriter root rootIn matched] at run
    cases run
    rfl
  | some assignment =>
    obtain ⟨_rooted, region, parent, _ssa, regions⟩ := admissible assignment matched
    obtain ⟨block, rootParent, _⟩ := OperationPtr.getParentRegion!_eq_some_iff.mp parent
    have attached : (root.getParent! rewriter.ctx.raw).isSome = true := by simp [rootParent]
    have equal := rule.compile_eq_of_no_action_of_safe_root attached regions run noAction
    simpa only using congrArg PatternRewriter.ctx equal

/-- Greedy compilation is sound at every visited root when placement obligations are supplied
only for rules whose concrete matcher succeeds at that root. -/
theorem valid_rules_greedy_moduleRefinement_of_matches
    (rules : Array (Veir.Puddle.Pattern OpCode))
    (valid : ∀ rule ∈ rules, Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    (rootIn : root.InBounds rewriter.ctx.raw)
    (moduleCode : moduleOp.getOpType! rewriter.ctx.raw = .builtin .module)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (moduleNoParent : moduleOp.getParent! rewriter.ctx.raw = none)
    (admissible : ∀ rule ∈ rules, ∀ assignment, rule.matcher.run rewriter.ctx.raw root = some assignment →
      RootAdmissible rewriter.ctx moduleOp root)
    (run : RewritePattern.GreedyRewritePattern (rules.map (fun rule => rule.compile.run))
      rewriter root rootIn = some result) :
    moduleOp.isModuleRefinedByCTree rewriter.ctx moduleOp result.ctx ∧ result.ctx.Verified moduleOp ∧
      moduleOp.getOpType! result.ctx.raw = .builtin .module ∧ moduleOp.getParent! result.ctx.raw = none := by
  let relation (before after : WfIRContext OpCode) : Prop :=
    moduleOp.isModuleRefinedByCTree before moduleOp after ∧ after.Verified moduleOp ∧
      moduleOp.getOpType! after.raw = .builtin .module ∧ moduleOp.getParent! after.raw = none
  apply RewritePattern.greedy_context_relation (rules.map (fun rule => rule.compile.run)) relation
    (before := rewriter) (after := result) (op := root) (inBounds := rootIn) ?_ ?_ ?_ run
  · exact ⟨OperationPtr.isModuleRefinedByCTree_refl sourceVerified moduleOp,
      sourceVerified, moduleCode, moduleNoParent⟩
  · intro pattern member attempt next attemptIn context ran noAction
    obtain ⟨rule, ruleMember, rfl⟩ := Array.mem_map.mp member
    apply (valid rule ruleMember).compile_ctx_eq_of_no_action_of_matches attemptIn
      (by simpa only [context] using sourceVerified) ?_ ran noAction
    intro assignment matched
    have initialMatch : rule.matcher.run rewriter.ctx.raw root = some assignment := by
      simpa only [context] using matched
    simpa only [context] using admissible rule ruleMember assignment initialMatch
  · intro pattern member attempt next attemptIn context ran
    obtain ⟨rule, ruleMember, rfl⟩ := Array.mem_map.mp member
    apply (valid rule ruleMember).compile_moduleRefinement_of_matches attemptIn
      (by simpa only [context] using moduleCode) (by simpa only [context] using sourceVerified)
      (by simpa only [context] using moduleNoParent) ?_ ran
    intro assignment matched
    have initialMatch : rule.matcher.run rewriter.ctx.raw root = some assignment := by
      simpa only [context] using matched
    simpa only [context] using admissible rule ruleMember assignment initialMatch

end
end Veir.Puddle.CTree
