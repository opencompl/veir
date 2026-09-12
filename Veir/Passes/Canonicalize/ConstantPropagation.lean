module

public import Veir.PatternRewriter.Basic
public import Veir.GlobalOpInfo
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

/-- Block arguments have no defining dialect, so choose a materializer by type. -/
private def blockArgumentMaterializer (type : TypeAttr) : Option OpCode :=
  match type.val with
  | .integerType _ => some (.arith .constant)
  | .modArithType _ => some (.mod_arith .constant)
  | _ => none

/--
Try ordinary folding first. If it does not produce replacements, use the
analysis to materialize constant results and constant block arguments used by
this operation. Replacing a block argument enqueues its users, so the greedy
driver retries folding with the newly materialized operands.
-/
public def tryFoldWithAnalysis (dfCtx : DataFlowContext)
    (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let opType := op.getOpType rewriter.ctx.raw opInBounds
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  let resultTypes := op.getResultTypes rewriter.ctx.raw opInBounds
  let properties := op.getProperties rewriter.ctx.raw opType opInBounds (by grind)
  let (rewriter, replacements) ←
    rewriter.tryFold! opType properties resultTypes operands (.before op)
  if let some replacements := replacements then
    let mut rewriter := rewriter
    for (replacement, index) in replacements.zipIdx do
      rewriter := rewriter.replaceValue! (op.getResult index) replacement
    return rewriter.eraseOp! op

  let mut rewriter := rewriter
  -- Replacing an existing constant would keep creating equivalent constants.
  if !opType.isConstantLike then
    for result in op.getResults! rewriter.ctx.raw do
      rewriter ← replaceConstant rewriter dfCtx result opType (.before op)
  for operand in operands do
    let .blockArgument argument := operand | continue
    let some materializer := blockArgumentMaterializer (operand.getType! rewriter.ctx.raw)
      | continue
    rewriter ← replaceConstant rewriter dfCtx operand materializer
      (InsertPoint.atStart! argument.block rewriter.ctx.raw)
  if op.isTriviallyDead rewriter.ctx.raw then
    rewriter := rewriter.eraseOp! op
  return rewriter

end Veir.Canonicalize
