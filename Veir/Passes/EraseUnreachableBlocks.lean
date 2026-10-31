module

public import Veir.Pass
public import Veir.Rewriter.EraseUnreachableBlocks

namespace Veir

/-! We implement a pass erasing the blocks that are unreachable from the entry of their region. -/

def EraseUnreachableBlocksPass.impl (ctx : WfIRContext OpCode) (op : OperationPtr)
    (_ : op.InBounds ctx.raw) : ExceptT String IO (WfIRContext OpCode) := do
  match WfRewriter.eraseUnreachableBlocksIn? ctx op with
  | none => throw "Error while erasing unreachable blocks"
  | some ctx => pure ctx

public def EraseUnreachableBlocksPass : Pass OpCode :=
  { name := "erase-unreachable-blocks"
    description := "Erase the blocks that are unreachable from the entry block of their region, together with everything nested in them."
    run := fun _ => EraseUnreachableBlocksPass.impl }
