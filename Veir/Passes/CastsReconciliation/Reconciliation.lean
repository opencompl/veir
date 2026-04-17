import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.DCE.dce

namespace Veir

/-!
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!reg` and `i64` types.
-/
set_option warn.sorry false in
def reconcileRegistersPairingCast (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some cast := matchCastOp op rewriter.ctx | return rewriter
  let input := op.getOperand! rewriter.ctx.raw 0
  let inputType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  /- Only consider casting between `!reg` and `i64` types-/
  if ¬ (inputType = RegisterType.mk ∧ resultType = IntegerType.mk 64) ∧
       ¬ (inputType = IntegerType.mk 64 ∧ resultType = RegisterType.mk) then return rewriter
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return rewriter
  let some cast := matchCastOp op'.op rewriter.ctx | return rewriter
  let parentInput := (op'.op.getOperand! rewriter.ctx.raw 0)
  /- And the result's type coincides with the parent operation operand's type -/
  let parentInputType := parentInput.getType! rewriter.ctx.raw
  if resultType ≠ parentInputType then return rewriter
  /- Replace the initial operation's output with the parent operations input -/
  let rewriter ← rewriter.replaceValue (op.getResult 0) parentInput sorry sorry
  /- Erase the redundant cast operation -/
  let rewriter ← rewriter.eraseOp op sorry sorry sorry
  /- If unused and side-effect-free, erase the parent cast operation as well.
    These need to be erased in this order, otherwise the parent operation will always be used. -/
  if ¬ op'.op.hasUses! rewriter.ctx.raw && hasSideEffects rewriter op'.op then
    rewriter.eraseOp op'.op sorry sorry sorry
  else
    return rewriter

/-!
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `iX` and `iY` types,
  of the form:
  ```
  %x = "builtin.unrealized_conversion_cast"(%s) : (iX) -> iY
  %y = "builtin.unrealized_conversion_cast"(%x) : (iY) -> iX
  ```
  where `X ≤ Y`, to ensure no information is loss and correctness is preserved.
  Note that reconciliation matches the second casting operation, therefore
  we need to check that the width of the result type is less than - or equal to the input's width.
-/
set_option warn.sorry false in
def reconcileIntegersPairingCast (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some cast := matchCastOp op rewriter.ctx.raw | return rewriter
  let input := op.getOperand! rewriter.ctx.raw 0
  let inputType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  /- Only consider casting between `!reg` and `i64` types-/
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  let IntegerType.mk bwRes := resultType | return rewriter
  let IntegerType.mk bwIn := inputType | return rewriter
  if bwIn ≤ bwRes then return rewriter
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return rewriter
  let some cast := matchCastOp op'.op rewriter.ctx.raw | return rewriter
  let parentInput := (op'.op.getOperand! rewriter.ctx.raw 0)
  /- And the result's type coincides with the parent operation operand's type -/
  let parentInputType := parentInput.getType! rewriter.ctx.raw
  if resultType ≠ parentInputType then return rewriter
  /- Replace the initial operation's output with the parent operations input -/
  let rewriter ← rewriter.replaceValue (op.getResult 0) parentInput sorry sorry
  /- Erase the redundant cast operation -/
  let rewriter ← rewriter.eraseOp op sorry sorry sorry
  /- If unused and side-effect-free, erase the parent cast operation as well.
    These need to be erased in this order, otherwise the parent operation will always be used. -/
  if ¬ op'.op.hasUses! rewriter.ctx.raw && hasSideEffects rewriter op'.op then
    rewriter.eraseOp op'.op sorry sorry sorry
  else
    return rewriter

set_option warn.sorry false in
def reconcileIdentityCast (rewriter : PatternRewriter OpCode) (op : OperationPtr) :
    Option (PatternRewriter OpCode) := do
  let some cast := matchCastOp op rewriter.ctx.raw | return rewriter
  /- get the input and output types -/
  let input := op.getOperand! rewriter.ctx.raw 0
  let inputType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  if inputType ≠ resultType then return rewriter
  let rewriter ← rewriter.replaceValue (op.getResult 0) input sorry sorry
  rewriter.eraseOp op sorry sorry sorry

def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[reconcileIntegersPairingCast, reconcileRegistersPairingCast, reconcileIdentityCast]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying cast reconciliation"
  | some ctx => pure ctx

public def CastReconcilePass : Pass OpCode :=
  { name := "reconcile-cast"
    description := "Reconcile casts where the input and output types are the same."
    run := CastReconcilePass.impl }
