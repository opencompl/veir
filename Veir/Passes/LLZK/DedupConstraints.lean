module

public import Veir.Pass
import Veir.Rewriter.WfRewriter

/-!
# Constraint deduplication for LLZK

Removes repeated `constrain.eq` operand pairs within each block. The pass uses a
stateful traversal because matching depends on earlier operations.
-/

namespace Veir
namespace LLZK
namespace DedupConstraints

public section

/-- An ordered `constrain.eq` operand pair. -/
structure Key where
  lhs : ValuePtr
  rhs : ValuePtr
deriving DecidableEq, BEq, Hashable

/-- `some key` when `op` is a `constrain.eq`, `none` otherwise. -/
def key? (ctx : IRContext OpCode) (op : OperationPtr) : Option Key :=
  match op.getOpType! ctx with
  | .constrain .eq => some { lhs := op.getOperand! ctx 0, rhs := op.getOperand! ctx 1 }
  | _ => none

/-- Deduplicate the `constrain.eq` operations of a single block. -/
def dedupBlock (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (_hblk : blk.InBounds ctx.raw := by grind) : WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  let mut maybeOp := (blk.get! ctx.raw).firstOp
  let mut seen : Std.HashSet Key := ∅
  while h : maybeOp.isSome do
    let op := maybeOp.get h
    let next := (op.get! ctx.raw).next
    if let some k := key? ctx.raw op then
      if seen.contains k then
        ctx := WfRewriter.eraseOp! ctx op
      else
        seen := seen.insert k
    maybeOp := next
  return ctx

/-- Every block nested under `op`. -/
partial def blocksUnder (ctx : IRContext OpCode) (op : OperationPtr) : _root_.Array BlockPtr := Id.run do
  let mut acc : _root_.Array BlockPtr := #[]
  for region in (op.get! ctx).regions do
    let mut b := (region.get! ctx).firstBlock
    while let some blk := b do
      acc := acc.push blk
      let mut o := (blk.get! ctx).firstOp
      while let some inner := o do
        acc := acc ++ blocksUnder ctx inner
        o := (inner.get! ctx).next
      b := (blk.get! ctx).next
  return acc

/-- Run deduplication over every block under `top`. -/
def run (ctx : WfIRContext OpCode) (top : OperationPtr) : WfIRContext OpCode := Id.run do
  let mut ctx := ctx
  for blk in blocksUnder ctx.raw top do
    if h : blk.InBounds ctx.raw then
      ctx := dedupBlock ctx blk h
  return ctx

def impl (ctx : WfIRContext OpCode) (op : OperationPtr) (_ : op.InBounds ctx.raw) :
    ExceptT _root_.String IO (WfIRContext OpCode) :=
  pure (run ctx op)

end

end DedupConstraints

public def DedupConstraintsPass : Pass OpCode :=
  { name := "llzk-dedup-constraints"
    description := "Remove `constrain.eq` operations that repeat an earlier assertion in the same block."
    run := fun _ => DedupConstraints.impl }

end LLZK
end Veir
