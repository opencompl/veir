import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Passes.DCE.dce

namespace Veir

/-!
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `!riscv.reg` and `i64` types.
-/
def isRiscvRegToI64Cast (inputType interType : TypeAttr): Bool :=
 match inputType.val, interType.val with
  | .registerType _, .integerType x => x.bitwidth = 64
  | .integerType x, .registerType _ => x.bitwidth = 64
  | _, _ => false

/-!
  We reconcile casts in `builtin.unrealized_conversion_cast` operations for `iX` and `iY` types,
  of the form:
  ```
  %x = "builtin.unrealized_conversion_cast"(%s) : (iX) -> iY
  %y = "builtin.unrealized_conversion_cast"(%x) : (iY) -> iX
  ```
  where `X ≤ Y`, to ensure no information is loss and correctness is preserved.
-/
def isPreservingIntegerTypeRoundTrip (inputType interType : TypeAttr) : Bool :=
  match inputType.val, interType.val with
  | .integerType x, .integerType y => x.bitwidth ≤ y.bitwidth
  | _, _ => false

/- Reconciles round-trip casts of the form X->Y->X if allowed for these types by `legal X Y` -/
def reconcilePairingCast (legal : TypeAttr → TypeAttr → Bool) (rewriter : PatternRewriter OpCode)
    (op : OperationPtr) (_ : op.InBounds rewriter.ctx.raw) :
    Option (PatternRewriter OpCode) := do
  let some _ := matchCastOp op rewriter.ctx.raw | return rewriter
  let input := op.getOperand! rewriter.ctx.raw 0
  /- Note that reconciliation matches on the second casting operation, so the input type of this op would be the intermediate type -/
  let interType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  /- If the operand's parent is a cast operation -/
  let .opResult op' := input | return rewriter
  let some _ := matchCastOp op'.op rewriter.ctx.raw | return rewriter
  let parentInput := (op'.op.getOperand! rewriter.ctx.raw 0)
  /- And the result's type coincides with the parent operation operand's type -/
  let inputType := parentInput.getType! rewriter.ctx.raw
  if resultType ≠ inputType then return rewriter
  /- And the reconciliation is legal -/
  if ¬ legal inputType interType then return rewriter
  /- Replace the initial operation's output with the parent operations input -/
  let rewriter := rewriter.replaceValue! (op.getResult 0) parentInput
  /- Erase the redundant cast operation -/
  let rewriter := rewriter.eraseOp! op
  /- If unused and side-effect-free, erase the parent cast operation as well.
    These need to be erased in this order, otherwise the parent operation will always be used. -/
  if ¬ op'.op.hasUses! rewriter.ctx.raw && ¬ op'.op.hasSideEffects rewriter.ctx.raw then
    return rewriter.eraseOp! op'.op
  else
    return rewriter

def reconcileIdentityCast (rewriter : PatternRewriter OpCode) (op : OperationPtr)
  (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let some _ := matchCastOp op rewriter.ctx.raw | return rewriter
  /- get the input and output types -/
  let input := op.getOperand! rewriter.ctx.raw 0
  let inputType := input.getType! rewriter.ctx.raw
  let resultType := ((op.getResult 0).get! rewriter.ctx.raw).type
  if inputType ≠ resultType then return rewriter
  let rewriter := rewriter.replaceValue! (op.getResult 0) input
  return rewriter.eraseOp! op

def CastReconcilePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[reconcilePairingCast isRiscvRegToI64Cast, reconcilePairingCast isPreservingIntegerTypeRoundTrip, reconcileIdentityCast]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying cast reconciliation"
  | some ctx => pure ctx

public def CastReconcilePass : Pass OpCode :=
  { name := "reconcile-cast"
    description := "Reconcile casts where the input and output types are the same."
    run := CastReconcilePass.impl }
