module

public import Veir.PatternRewriter.Basic
public import Veir.GlobalOpInfo
import Veir.Analysis.DataFlow.SparseConstantPropagationAnalysis

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
Walk the analyzed IR snapshot, replacing constant results and block arguments.
Only substitutions and removal of dead operations happen during this walk, so
facts about the original values remain applicable. Newly created constants are
not visited.
-/
private partial def rewriteConstants (op : OperationPtr) (irCtx : WfIRContext OpCode)
    (dfCtx : DataFlowContext) (rewriter : PatternRewriter OpCode) :
    Option (PatternRewriter OpCode) := do
  let mut rewriter := rewriter
  let operation := op.get! irCtx.raw
  if operation.parent.isSome && !operation.opType.isConstantLike then
    for result in op.getResults! irCtx.raw do
      rewriter ← replaceConstant rewriter dfCtx result operation.opType (.before op)

  for region in operation.regions do
    let mut maybeBlock := (region.get! irCtx.raw).firstBlock
    while let some block := maybeBlock do
      for argument in block.getArguments! irCtx.raw do
        let some materializer := blockArgumentMaterializer (argument.getType! irCtx.raw)
          | continue
        rewriter ← replaceConstant rewriter dfCtx argument materializer
          (InsertPoint.atStart! block rewriter.ctx.raw)
      let mut maybeOp := (block.get! irCtx.raw).firstOp
      while let some nestedOp := maybeOp do
        rewriter ← rewriteConstants nestedOp irCtx dfCtx rewriter
        maybeOp := (nestedOp.get! irCtx.raw).next
      maybeBlock := (block.get! irCtx.raw).next

  if operation.parent.isSome && op.isTriviallyDead rewriter.ctx.raw then
    rewriter := rewriter.eraseOp! op
  return rewriter

/--
Run sparse constant propagation once and apply its constant facts. Clean up
operations made dead by substitution without performing any further folding.
-/
public def propagateConstants (ctx : WfIRContext OpCode) (top : OperationPtr) :
    Option (WfIRContext OpCode) := do
  let dfCtx ← fixpointSolve top #[SparseConstantPropagationAnalysis] ctx
  let mut rewriter ← rewriteConstants top ctx dfCtx
    { ctx, hasDoneAction := false, worklist := .empty }
  -- Erasing an operation enqueues its operand definitions, so this also removes
  -- dead intermediate constants and producers left behind by the forward walk.
  while !rewriter.worklist.isEmpty do
    let (maybeOp, worklist) := rewriter.worklist.pop
    rewriter := { rewriter with worklist }
    if let some op := maybeOp then
      if op.InBounds rewriter.ctx.raw then
        if op.isTriviallyDead rewriter.ctx.raw then
          rewriter := rewriter.eraseOp! op
  return rewriter.ctx

end Veir.Canonicalize
