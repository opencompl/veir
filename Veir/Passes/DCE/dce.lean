module

public import Veir.Pass
public import Veir.PatternRewriter.Basic
public import Veir.Passes.StrictDriver

namespace Veir

/-! We implement a dead code elimination pass. -/

public def eliminateDeadOp (rewriter: PatternRewriter OpCode) (op: OperationPtr)
    (_opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  if op.isTriviallyDead rewriter.ctx.raw then
    return rewriter.eraseOp! op
  else
    return rewriter

/-- The strict pass: only the dead operations that the rewrite driver erases itself, which do not
allocate, are removed. Its soundness is `DCEPass.runStrict_sound`. -/
public def DCEPass.runStrict : PurePass :=
  strictContextPass "dce" (RewritePattern.GreedyRewritePattern #[])

public def DCEPass.impl (strict : Bool) (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) :=
  if strict then ExceptT.mk (pure (DCEPass.runStrict ctx op)) else do
    -- `eliminateDeadOp`, which also erases allocating operations, is unproven, so not run:
    -- the driver erases the dead operations that do not allocate.
    let pattern := RewritePattern.GreedyRewritePattern #[]
    match RewritePattern.applyInContext pattern ctx op with
    | none => throw "Error while applying DCE"
    | some ctx => pure ctx

public def DCEPass : Pass OpCode :=
  { name := "dce"
    description := "Eliminate trivially dead operations: no regions, no used results, no memory writes, and not a block terminator."
    options := .ofList [
      ("strict", { description :=
                     "Only erase dead operations that do not allocate, which is proved to refine the module.",
                   defaultValue := false })]
    run := fun options => DCEPass.impl ((options.get? "strict").getD false) }
