module

public import Veir.Interpreter.Basic

/-!
# ConstantLikeInterfaces

This file provides support for querying whether an operation materializes
a literal constant value, and for reading out the value it materializes.
-/

namespace Veir

public section

def OperationPtr.isConstantLike {OpInfo : Type} [HasOpInfo OpInfo]
    (op : OperationPtr) (ctx : IRContext OpInfo) : Bool :=
  HasDialectOpInfo.isConstantLike (op.getOpType! ctx)

def ValuePtr.isConstantLike {OpInfo : Type} [HasOpInfo OpInfo]
    (val : ValuePtr) (ctx : IRContext OpInfo) : Bool :=
  match val.getDefiningOp! ctx with
  | some defOp => defOp.isConstantLike ctx
  | none => false

/--
  If `val` is defined by a supported constant-like operation, return
  the runtime value it materializes. We materialize an appropriate
  poison value for operations that trigger UB.
-/
def ValuePtr.constantValue (val : ValuePtr) (ctx : IRContext OpCode) : Option RuntimeValue := do
  let .opResult res := val | none
  if ¬ res.op.isConstantLike ctx then none else
  -- Constant-like operations take no operands, but nothing checks that for
  -- us the way MLIR's trait verifier does, so check it here: it is what
  -- makes interpreting against an empty operand array and an empty memory
  -- produce exactly the value the operation materializes.
  if res.op.getNumOperands! ctx ≠ 0 then none else
  match (res.op.interpret ctx #[] .empty : Option (UBOr _)) with
  | some (.ok (results, _, none)) => results[res.index]?
  | some .ub => RuntimeValue.getPoisonForType (val.getType! ctx)
  | _ => none

end

end Veir
