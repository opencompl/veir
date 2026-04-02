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
  0 < op.getNumResults! rewriter.ctx

set_option warn.sorry false in
def eliminateDeadOp (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  /- delete operations that are not used and have no side effects -/
  if ¬ op.hasUses! rewriter.ctx && hasSideEffects rewriter op then
    rewriter.eraseOp op sorry
  else
    return rewriter

set_option warn.sorry false in
def DCEPass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreedyRewritePattern #[eliminateDeadOp]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying DCE"
  | some ctx => pure ⟨ctx, sorry⟩

public def DCEPass : Pass OpCode :=
  { name := "dce"
    description := "Eliminate dead code by removing operations whose results are unused."
    run := DCEPass.impl }
