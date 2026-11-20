module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
public import Veir.Passes.CheckedDriver

namespace Veir

/-! We implement a dead code elimination pass. -/

public def eliminateDeadOp (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.isTriviallyDead rewriter.ctx.raw then
    return rewriter.eraseOp! op
  else
    return rewriter

/-- The pass: the rewrite driver erases the dead operations that do not allocate.
`eliminateDeadOp`, which also erases allocating operations, is unproven, so not run. Its
soundness is `DCEPass.run_sound`. -/
public def DCEPass.run : PurePass :=
  checkedContextPass "dce" (RewritePattern.GreedyRewritePattern #[])

public def DCEPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT String IO (WfIRContext OpCode) :=
  ExceptT.mk (pure (DCEPass.run ctx op))

public def DCEPass : Pass OpCode :=
  { name := "dce"
    description := "Eliminate trivially dead operations: no regions, no used results, no memory writes, and not a block terminator."
    run := fun _ => DCEPass.impl }
