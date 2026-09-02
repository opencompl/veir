module

public import Veir.Pass
public import Veir.Dialects.LLZK.Semantics.Constraint
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

/-- Keep the first occurrence of each operand pair and erase later repeats. -/
def dedupOps (ctx : WfIRContext OpCode) (ops : List OperationPtr)
    (seen : Std.HashSet Key) : WfIRContext OpCode :=
  match ops with
  | [] => ctx
  | op :: rest =>
    match key? ctx.raw op with
    | none => dedupOps ctx rest seen
    | some k =>
      if seen.contains k then
        dedupOps (WfRewriter.eraseOp! ctx op) rest seen
      else
        dedupOps ctx rest (seen.insert k)

/-- Deduplicate the `constrain.eq` operations of a single block. -/
def dedupBlock (ctx : WfIRContext OpCode) (blk : BlockPtr)
    (hblk : blk.InBounds ctx.raw := by grind) : WfIRContext OpCode :=
  dedupOps ctx (Semantics.opsOf ctx blk hblk) ∅

/-- Every block nested under `op`. -/
partial def blocksUnder (ctx : IRContext OpCode) (op : OperationPtr) : Array BlockPtr := Id.run do
  let mut acc : Array BlockPtr := #[]
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
    ExceptT String IO (WfIRContext OpCode) :=
  pure (run ctx op)

end

end DedupConstraints

public def DedupConstraintsPass : Pass OpCode :=
  { name := "llzk-dedup-constraints"
    description := "Remove `constrain.eq` operations that repeat an earlier assertion in the same block."
    run := fun _ => DedupConstraints.impl }

end LLZK
end Veir
