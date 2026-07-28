module

public import Veir.Interpreter.Basic
public import Veir.Interfaces.ConstantLikeInterfaces

public section

namespace Veir

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
  | some .ub =>
    match (val.getType! ctx).val with
    | .integerType intTy => some (.int intTy.bitwidth .poison)
    | .byteType byteTy => some (.byte byteTy.bitwidth Data.LLVM.Byte.allPoison)
    | _ => none
  | _ => none

end Veir
