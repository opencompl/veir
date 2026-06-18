import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching

namespace Veir

/-!
  # Canonicalize pass

  Currently, the only transformation it performs is to move constants
  to the right side, for commutative operations.
-/

def isConstOperand (ctx : IRContext OpCode) (v : ValuePtr) : Bool :=
  match v.getDefiningOp! ctx with
  | some defOp => (defOp.getOpType! ctx).isConstantLike
  | none => false

set_option warn.sorry false in
def commutativeConstantRHS (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (_ : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType! rewriter.ctx.raw
  if ¬ opType.isCommutative then return rewriter
  let operands := op.getOperands! rewriter.ctx.raw
  /- Stable partition: non-constant operands first, then the constants. -/
  let (nonConsts, consts) := operands.partition (!isConstOperand rewriter.ctx.raw ·)
  let reordered := nonConsts ++ consts
  if reordered == operands then return rewriter
  let resultTypes := op.getResultTypes! rewriter.ctx.raw
  let properties := op.getProperties! rewriter.ctx.raw opType
  let (rewriter, newOp) ← rewriter.createOp opType resultTypes reordered
    #[] #[] properties (some $ .before op) sorry sorry sorry sorry
  rewriter.replaceOp op newOp sorry sorry sorry sorry sorry

/-! ## Pass implementation -/

def CanonicalizePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    commutativeConstantRHS
  ]
  match RewritePattern.applyInContext pattern ctx with
  | none => throw "Error while applying canonicalization patterns"
  | some ctx => pure ctx

public def CanonicalizePass : Pass OpCode :=
  { name := "canonicalize"
    description := "Rewrite operations into a canonical form."
    run := CanonicalizePass.impl }

end Veir
