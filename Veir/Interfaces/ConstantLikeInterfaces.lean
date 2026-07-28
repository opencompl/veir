module

public import Veir.IR.Basic

/-!
# ConstantLikeInterfaces

This file provides support for querying whether an operation materializes
a literal constant value.
-/

namespace Veir

public section

def OperationPtr.isConstantLike {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  HasOpInfo.isConstantLike (op.getOpType! ctx)

def ValuePtr.isConstantLike {OpInfo : Type} [HasOpInfo OpInfo]
    (val : ValuePtr) (ctx : IRContext OpInfo) : Bool :=
  match val.getDefiningOp! ctx with
  | some defOp => defOp.isConstantLike ctx
  | none => false

end

end Veir
