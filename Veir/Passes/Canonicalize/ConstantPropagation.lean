module

public import Veir.PatternRewriter.Basic
public import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis
import Veir.Interfaces.FoldInterfaces
import Veir.Interfaces.ControlFlowInterfaces

namespace Veir.Canonicalize

private def replaceConstant (rewriter : PatternRewriter OpCode)
    (dfCtx : DataFlowContext) (value : ValuePtr) (materializer : OpCode) :
    Option (PatternRewriter OpCode) := do
  if !value.hasUses! rewriter.ctx.raw then return rewriter
  let .constant constant := SparseFact.getElement .sparseConstant value dfCtx
    | return rewriter
  let type := value.getType! rewriter.ctx.raw
  let some ⟨constOp, properties⟩ := materializer.materializeConstant
      (.int constant.bitwidth constant.value) type
    | return rewriter
  let insertionPoint : InsertPoint := match value with
    | .opResult result => .before result.op
    | .blockArgument argument => InsertPoint.atStart! argument.block rewriter.ctx.raw
  let (rewriter, op) ← rewriter.createOp! constOp #[type] #[] #[] #[] properties
    (some insertionPoint)
  return rewriter.replaceValue! value (op.getResult 0)

/--
A block argument has no defining operation, so take the dialect from a value some
predecessor forwards into this argument position.
-/
private def blockArgumentMaterializer
    (argument : BlockArgumentPtr) (ctx : IRContext OpCode) : OpCode := Id.run do
  let mut maybeUse := (argument.block.get! ctx).firstUse
  while let some use := maybeUse do
    let useStruct := use.get! ctx
    maybeUse := useStruct.nextUse
    let some forwarded :=
        BranchOpInterface.getSuccessorOperand? useStruct.owner use.index argument.index ctx
      | continue
    let some definingOp := forwarded.definingOp? | continue
    return definingOp.getOpType! ctx
  .arith .constant

private def propagateConstants (dfCtx : DataFlowContext)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType rewriter.ctx.raw opInBounds
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  if opType.isConstantLike then return rewriter
  let mut rewriter := rewriter
  for result in op.getResults! rewriter.ctx.raw do
    rewriter ← replaceConstant rewriter dfCtx result opType
  for operand in operands do
    let .blockArgument argument := operand | continue
    rewriter ← replaceConstant rewriter dfCtx operand
      (blockArgumentMaterializer argument rewriter.ctx.raw)
  return rewriter

/--
Try ordinary folding first, then materialize constants inferred by the analysis.
Replacing a block argument enqueues its users, so the greedy driver retries
folding with the newly materialized operands.
-/
public def tryFoldWithAnalysis (dfCtx : DataFlowContext) : RewritePattern OpCode :=
  .GreedyRewritePattern #[foldOperation, propagateConstants dfCtx]

end Veir.Canonicalize
