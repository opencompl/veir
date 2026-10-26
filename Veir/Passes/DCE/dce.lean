module

public import Veir.Pass
public import Veir.PatternRewriter.Basic

namespace Veir

/-! We implement a dead code elimination pass. -/

public def eliminateDeadOp (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.isTriviallyDead rewriter.ctx.raw then
    return rewriter.eraseOp! op
  else
    return rewriter

/-- The pure transformation executed by DCE's pass wrapper. -/
@[expose]
public def DCEPass.transform (ctx : WfIRContext OpCode) : Option (WfIRContext OpCode) :=
  RewritePattern.applyInContext (RewritePattern.GreedyRewritePattern #[eliminateDeadOp]) ctx

def DCEPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  match DCEPass.transform ctx with
  | none => throw "Error while applying DCE"
  | some ctx => pure ctx

public def DCEPass : Pass OpCode :=
  { name := "dce"
    description := "Eliminate trivially dead operations: no regions, no used results, no memory writes or allocations, and not a block terminator."
    run := fun _ => DCEPass.impl }
