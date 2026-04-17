import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-! We implement a dead code elimination pass. -/

/--
  An operation is considered to have side effects if it has zero results.

  TODO: replace this with a side-effect property on `OpCode`.
-/
def hasSideEffects (rewriter: PatternRewriter OpCode) (op: OperationPtr) : Bool :=
  0 < op.getNumResults! rewriter.ctx.raw

set_option warn.sorry false in
def eliminateDeadOp (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  /- delete operations that are not used and have no side effects -/
  if ¬ op.hasUses! rewriter.ctx.raw && hasSideEffects rewriter op then
    rewriter.eraseOp op sorry sorry sorry
  else
    return rewriter

def DCEPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[eliminateDeadOp]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying DCE"
  | some ctx => pure ctx

public def DCEPass : Pass OpCode :=
  { name := "dce"
    description := "Eliminate dead code by removing operations whose results are unused."
    run := DCEPass.impl }
