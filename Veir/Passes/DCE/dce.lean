import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-! We implement a dead code elimination pass. -/

set_option warn.sorry false in

def eliminateDeadOp (rewriter: PatternRewriter OpCode) (op: OperationPtr) :
    Option (PatternRewriter OpCode) := do
  /- delete operations that are not used and return at least one result.
    with the second condition we ensure not to delete operations like `func.func` that
    return nothing but wrap the entire module at a higher level. -/
  if ¬ op.hasUses! rewriter.ctx  && 0 < op.getNumResults! rewriter.ctx then
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
