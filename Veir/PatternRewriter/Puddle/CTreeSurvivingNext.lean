module
public import Veir.PatternRewriter.Puddle.CTreeSurvivingStep
public import Veir.Verifier.FunctionControlFlow
import all Veir.PatternRewriter.Puddle.CTreeRewriteInvariant
import all Veir.PatternRewriter.Puddle.CTreeSurvivingStep
import all Veir.PatternRewriter.Puddle.CTreeModuleSoundness
import all Veir.IR.Basic
import all Veir.IRNesting
import all Veir.Dominance.Basic
import all Veir.Rewriter.InsertPoint

namespace Veir.Puddle.CTree
public section

/-- The concrete successor of a surviving instruction is the redirected source successor.
The post-instruction state invariant therefore supplies the next instruction invariant. -/
theorem Pattern.Valid.surviving_next
    {rule : Veir.Puddle.Pattern OpCode} (valid : Pattern.Valid rule)
    {rewriter result : PatternRewriter OpCode} {root moduleOp : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpCode}
    {newOps : Array OperationPtr} {replacements : Array ValuePtr}
    {rootRegion body : RegionPtr} {function : OperationPtr}
    (sourceDom : rewriter.ctx.Dom moduleOp)
    (sourceVerified : rewriter.ctx.Verified moduleOp)
    (rootRooted : root.RootedAt moduleOp rewriter.ctx)
    (rootParentRegion : root.getParentRegion! rewriter.ctx.raw = some rootRegion)
    (rootSSA : rootRegion.hasSSADominance rewriter.ctx)
    (rootReachable : root.HierarchicallyReachable rewriter.ctx)
    (localRun : rule.interpret rewriter.ctx root = some (created, some (newOps, replacements)))
    (run : RewritePattern.fromLocalRewrite rule.interpret rewriter root rootIn = some result)
    (attached : (root.getParent! rewriter.ctx.raw).isSome = true)
    (regions : root.getNumRegions! rewriter.ctx.raw = 0)
    (functionCode : function.getOpType! rewriter.ctx.raw = .func .func)
    (bodyParent : body.getParent! rewriter.ctx.raw = some function)
    {mapping : ValueMapping rewriter.ctx result.ctx}
    {op next : OperationPtr} (sourceIn : op.InBounds rewriter.ctx.raw)
    (targetIn : op.InBounds result.ctx.raw) (different : op ≠ root)
    {sourceBlock targetBlock : BlockPtr}
    (sourceParent : op.getParent! rewriter.ctx.raw = some sourceBlock)
    (targetParent : op.getParent! result.ctx.raw = some targetBlock)
    (sourceBlockParent : sourceBlock.getParent! rewriter.ctx.raw = some body)
    (targetBlockParent : targetBlock.getParent! result.ctx.raw = some body)
    (sourceReachable : op.HierarchicallyReachable rewriter.ctx)
    (targetReachable : op.HierarchicallyReachable result.ctx)
    {sourceState : InterpreterState rewriter.ctx} {targetState : InterpreterState result.ctx}
    (post : RewritePointInvariant mapping root body
      (.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn)
      (.after op result.ctx.raw targetBlock targetParent targetIn) (by grind) (by grind)
      sourceState targetState)
    (sourceNext : op.getNextOp! rewriter.ctx.raw = some next) :
    ∃ (targetNext : OperationPtr) (targetNextIn : targetNext.InBounds result.ctx.raw),
      op.getNextOp! result.ctx.raw = some targetNext ∧
      RewriteOpInvariant mapping root newOps body body ⟨next, by grind⟩ ⟨targetNext, targetNextIn⟩
        sourceState targetState := by
  have contract := valid.replacement_contract_of_interpret sourceDom rootRooted rootParentRegion rootSSA
    rootReachable rootIn localRun
  have targetRedirect := Pattern.fromLocalRewrite_next_redirect rule localRun run attached regions contract.1
    sourceIn different
  rw [sourceNext] at targetRedirect
  simp only [Option.bind_some] at targetRedirect
  have existsRedirect : ∃ targetNext, redirectedOperation rewriter.ctx.raw root newOps next = some targetNext := by
    by_cases same : next = root
    · subst next
      have rootParent : root.getParent! rewriter.ctx.raw = some sourceBlock := by grind
      obtain ⟨following, follows⟩ := sourceVerified.nonterminator_hasNext_in_func (by grind) functionCode
        bodyParent sourceBlockParent rootParent (valid.root_nonterminator_of_interpret localRun)
      unfold redirectedOperation
      simp only [↓reduceIte]
      cases head : newOps[0]? with
      | none => exact ⟨following, by simp [follows]⟩
      | some first => exact ⟨first, rfl⟩
    · exact ⟨next, by simp [redirectedOperation, same]⟩
  obtain ⟨targetNext, redirection⟩ := existsRedirect
  have targetNextEq : op.getNextOp! result.ctx.raw = some targetNext := targetRedirect.trans redirection
  have nextIn : next.InBounds rewriter.ctx.raw := by grind
  have targetNextIn : targetNext.InBounds result.ctx.raw := by grind
  have nextParent : next.getParent! rewriter.ctx.raw = some sourceBlock := by grind
  have targetNextParent : targetNext.getParent! result.ctx.raw = some targetBlock := by grind
  have sourceAfter : InsertPoint.after op rewriter.ctx.raw sourceBlock sourceParent sourceIn = .before next :=
    InsertPoint.after_eq_of_some_next sourceNext
  have targetAfter : InsertPoint.after op result.ctx.raw targetBlock targetParent targetIn = .before targetNext :=
    InsertPoint.after_eq_of_some_next targetNextEq
  simp only [sourceAfter, targetAfter] at post
  refine ⟨targetNext, targetNextIn, targetNextEq, ?_⟩
  refine ⟨redirection, ?_, ?_, ?_, ?_, post.states, post.sourceDefined, post.targetDefined,
    post.matcherValues, post.matcherDefined, post.matcherHistory⟩
  · grind
  · grind
  · exact OperationPtr.HierarchicallyReachable.of_parent_block
      (sourceReachable.parent_block sourceParent) nextParent
  · exact OperationPtr.HierarchicallyReachable.of_parent_block
      (targetReachable.parent_block targetParent) targetNextParent

end
end Veir.Puddle.CTree
