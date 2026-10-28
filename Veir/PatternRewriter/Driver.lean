module

public import Veir.PatternRewriter.Basic
public import Veir.Interfaces.FoldInterfaces

/-!
  # Greedy rewrite driver

  Applies a rewrite pattern to every operation in a context until no more changes occur. As in
  MLIR's greedy driver, each operation is folded before the pattern is tried, so every pattern
  gets constant folding of the operations it creates.
-/

public section

namespace Veir

/--
- Apply the given rewrite pattern to all operations in the context (possibly multiple times),
  first folding each operation if `fold` is set.
- Return the new context, and a boolean indicating whether any changes were made.
- If any pattern failed, return none.
-/
private partial def RewritePattern.applyOnceInContext
    (pattern: RewritePattern OpCode) (fold : Bool) (ctx: WfIRContext OpCode) :
    Option (Bool × WfIRContext OpCode) := do
  let worklist := PatternRewriter.Worklist.createFromContext ctx
  let mut rewriter : PatternRewriter OpCode := { ctx, hasDoneAction := false, worklist }
  while !rewriter.worklist.isEmpty do
    let (opOpt, newWorklist) := rewriter.worklist.pop
    let op := opOpt.get!
    rewriter := { rewriter with worklist := newWorklist }
    if hin : op.InBounds rewriter.ctx.raw then
      -- Erase trivially dead operations directly, as in MLIR's greedy driver.
      if hdead : op.isTriviallyDead rewriter.ctx.raw then
        rewriter := rewriter.eraseOp op hdead.1 hdead.2.1 hin
      else
        let unchanged := { rewriter with hasDoneAction := false }
        let folded ← if fold then foldOperation unchanged op hin else pure unchanged
        -- A folded operation is erased, so the pattern is not tried on it.
        if folded.hasDoneAction then
          rewriter := folded
        else if hin : op.InBounds folded.ctx.raw then
          rewriter ← pattern { folded with hasDoneAction := rewriter.hasDoneAction } op hin
        else
          failure
    else
      failure
  pure (rewriter.hasDoneAction, rewriter.ctx)

def RewritePattern.applyInContext (pattern: RewritePattern OpCode)
    (ctx: WfIRContext OpCode) (fold : Bool := true) : Option (WfIRContext OpCode) := do
  let mut hasDoneAction := true
  let mut ctx := ctx
  while hasDoneAction do
    let (lastHasDoneAction, newCtx) ← pattern.applyOnceInContext fold ctx
    ctx := newCtx
    hasDoneAction := lastHasDoneAction
  pure ctx

end Veir
