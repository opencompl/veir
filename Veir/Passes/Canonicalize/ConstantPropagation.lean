module

public import Veir.PatternRewriter.Basic
public import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
import Veir.Interfaces.FoldInterfaces

namespace Veir.Canonicalize

/-- Materialize one inferred constant at a point that dominates all its uses. -/
private def replaceConstant (rewriter : PatternRewriter OpCode)
    (dfCtx : DataFlowContext) (value : ValuePtr) (materializer : OpCode)
    (insertionPoint : InsertPoint) : Option (PatternRewriter OpCode) := do
  if !value.hasUses! rewriter.ctx.raw then return rewriter
  let .constant constant := SparseFact.getElement .sparseConstant value dfCtx
    | return rewriter
  let type := value.getType! rewriter.ctx.raw
  let some ⟨constOp, properties⟩ := materializer.materializeConstant
      (.int constant.bitwidth constant.value) type
    | return rewriter
  let (rewriter, op) ← rewriter.createOp! constOp #[type] #[] #[] #[] properties
    (some insertionPoint)
  return rewriter.replaceValue! value (op.getResult 0)

private def propagateConstants (dfCtx : DataFlowContext)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType rewriter.ctx.raw opInBounds
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  if opType.isConstantLike then return rewriter
  let mut rewriter := rewriter
  for result in op.getResults! rewriter.ctx.raw do
    rewriter ← replaceConstant rewriter dfCtx result opType (.before op)
  for operand in operands do
    let .blockArgument argument := operand | continue
    -- Block arguments have no defining dialect. The materializer checks the type.
    let materializer : OpCode := match (operand.getType! rewriter.ctx.raw).val with
      | .modArithType _ => .mod_arith .constant
      | _ => .arith .constant
    rewriter ← replaceConstant rewriter dfCtx operand materializer
      (InsertPoint.atStart! argument.block rewriter.ctx.raw)
  return rewriter

/--
Try ordinary folding first, then materialize constants inferred by the analysis.
Replacing a block argument enqueues its users, so the greedy driver retries
folding with the newly materialized operands.
-/
public def tryFoldWithAnalysis (dfCtx : DataFlowContext) : RewritePattern OpCode :=
  .GreedyRewritePattern #[foldOperation, propagateConstants dfCtx]

end Veir.Canonicalize
