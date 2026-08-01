module

public import Veir.Interfaces.ConstantLikeInterfaces
public import Veir.Interpreter.Basic
public import Veir.Interpreter.Evaluate

/-!
  # Constant folding decision interface

  This file is the public entry point for deciding whether operations fold. It
  does not provide IR mutation or constant materialization.
-/

public section

namespace Veir

inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its constant-defined operands (`constOperands[i] =
  some rv` iff operand `i` is known to hold the constant `rv`). Operations with
  all operands constant are evaluated with the interpreter, and
  interpreter-reported UB becomes a poison constant. `none` means the operation
  does not fold with the supplied operand information.
-/
def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : Option FoldDecision := do
  guard (!opType.isConstantLike)
  let values ← constOperands.mapM id
  let #[resultType] := resultTypes | none
  match ← (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
  | .ok results =>
    let result ← results[0]?
    guard (result.Conforms resultType)
    return .useConstant result
  | .ub =>
    let .integerType intTy := resultType.val | none
    return .useConstant (.int intTy.bitwidth .poison)

/--
  Read-only convenience wrapper around `foldDecision` for an existing operation.
  The supplied constant array remains explicit so SCCP can provide constants
  inferred from lattice facts rather than only constants materialized in the IR.
-/
def foldDecisionForOp (op : OperationPtr)
    (ctx : WfIRContext OpCode) (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : Option FoldDecision := do
  guard (constOperands.size = op.getNumOperands ctx.raw opInBounds)
  let opType := op.getOpType ctx.raw opInBounds
  foldDecision opType
    (op.getProperties ctx.raw opType opInBounds (by grind))
    (op.getResultTypes ctx.raw opInBounds) constOperands

end Veir
