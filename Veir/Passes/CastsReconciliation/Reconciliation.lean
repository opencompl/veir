import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir
set_option warn.sorry false in
/-- Removes a cast from type A to type A, replacing the result with the operand. -/
def reconcileIdentityCast (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some cast := matchCastOp op rewriter.ctx | return rewriter
  /- get the input and output types -/
  let input := op.getOperand! rewriter.ctx 0
  let inputType := input.getType! rewriter.ctx
  let resultType := ((op.getResult 0).get! rewriter.ctx).type
  if inputType ≠ resultType then return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) input sorry sorry
  rewriter.eraseOp op sorry

def CastReconcilePass.impl (ctx : { ctx' : IRContext OpCode // ctx'.WellFormed }) (op : OperationPtr)
    (_ : op.InBounds ctx.val) :
    ExceptT String IO { ctx' : IRContext OpCode // ctx'.WellFormed } := do
  let pattern := RewritePattern.GreedyRewritePattern #[reconcileIdentityCast]
  match RewritePattern.applyInContext pattern ctx ctx.property.inBounds with
  | none => throw "Error while applying cast reconciliation"
  | some ctx => pure ⟨ctx, sorry⟩

public def CastReconcilePass : Pass OpCode :=
  { name := "reconcile-cast"
    description := "Reconcile casts where the input and output types are the same."
    run := CastReconcilePass.impl }
