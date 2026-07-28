module

public import Veir.IR.Basic

/-!
# ConstantLikeInterfaces

This file provides support for querying whether an operation materializes
a literal constant value.

Upstream this is an op trait rather than an interface, and its contract is
"non-side effecting operations with one result and zero operands that can
always be folded to a specific attribute value".

Also see:
https://github.com/llvm/llvm-project/blob/main/mlir/include/mlir/IR/OpDefinition.h
-/

namespace Veir

public section

/--
  Does this operation materialize a literal constant value: no operands,
  one result, no side effects, and a result that is always determined by
  the operation's properties?

  Consumers still have to obtain the value itself; this only says that
  asking for it is meaningful.
-/
def OperationPtr.isConstantLike {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  HasOpInfo.isConstantLike (op.getOpType! ctx)

/--
  Is this value defined by a constant-like operation? Block arguments
  never are.
-/
def ValuePtr.isConstantLike {OpInfo : Type} [HasOpInfo OpInfo]
    (val : ValuePtr) (ctx : IRContext OpInfo) : Bool :=
  match val.getDefiningOp! ctx with
  | some defOp => defOp.isConstantLike ctx
  | none => false

end

end Veir
