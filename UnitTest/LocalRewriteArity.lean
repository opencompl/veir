module

import Veir.PatternRewriter.Basic
import all Veir.PatternRewriter.Basic

namespace Veir.LocalRewriteArityTest

variable {OpInfo : Type} [HasOpInfo OpInfo]

/-- Invalid replacement counts fail before even attempting to insert the returned operations. -/
theorem mismatch_rejected {pattern : LocalRewritePattern OpInfo}
    {rewriter : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw} {created : WfIRContext OpInfo}
    {operations : Array OperationPtr} {values : Array ValuePtr}
    (localRun : pattern rewriter.ctx root = some (created, some (operations, values)))
    (mismatch : values.size ≠ root.getNumResults! created.raw) :
    RewritePattern.fromLocalRewrite pattern rewriter root rootIn = none := by
  simp [RewritePattern.fromLocalRewrite, localRun, guard, mismatch]

/-- A non-match never reaches the replacement-count check. -/
theorem no_match_unchanged {pattern : LocalRewritePattern OpInfo}
    {rewriter : PatternRewriter OpInfo} {root : OperationPtr}
    {rootIn : root.InBounds rewriter.ctx.raw}
    (localRun : pattern rewriter.ctx root = some (rewriter.ctx, none)) :
    RewritePattern.fromLocalRewrite pattern rewriter root rootIn =
      some { rewriter with hasDoneAction := false } := by
  simp [RewritePattern.fromLocalRewrite, localRun]

end Veir.LocalRewriteArityTest
