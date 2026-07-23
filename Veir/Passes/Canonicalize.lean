module

public import Veir.Pass
import Veir.PatternRewriter.Basic
import Veir.Passes.Matching
import Veir.Fold.Rewriter

namespace Veir

/-!
  # Canonicalize pass

  Performs the following transformations:
  * folding operations (see `Veir.Fold`);
  * moving constants to the right side, for commutative operations.
-/

def isConstOperand (ctx : IRContext OpCode) (v : ValuePtr) : Bool :=
  match v.getDefiningOp! ctx with
  | some defOp => (defOp.getOpType! ctx).isConstantLike
  | none => false

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
  rewriter.createOrFoldAndReplaceOp! op opType resultTypes reordered properties (.before op)

/-! ## Pass implementation -/

def CanonicalizePass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) := do
  let pattern := RewritePattern.GreedyRewritePattern #[
    foldOperation,
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
