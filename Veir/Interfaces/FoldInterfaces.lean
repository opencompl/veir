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
  /-- The operation does not fold with the supplied operand information. -/
  | noFold

/--
  Query whether an operation folds, given its result types and the values of
  its constant-defined operands (`constOperands[i] = some rv` iff operand `i`
  is defined by a constant-like operation with value `rv`).
-/
private def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  if !constOperands.all (·.isSome) then .noFold else
  let values := constOperands.map (·.get!)
  match resultTypes.toList with
  | [resultType] =>
    match (foldEvaluate opCode properties #[resultType] values : Option (UBOr _)) with
    | none => .noFold
    | some (.ok results) =>
      match results[0]? with
      | some result => if result.Conforms resultType then .useConstant result else .noFold
      | none => .noFold
    | some .ub =>
      match resultType.val with
      | .integerType intTy => .useConstant (.int intTy.bitwidth .poison)
      | _ => .noFold
  | _ => .noFold

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its known-constant operands. All-constant operations
  are evaluated with the interpreter, and interpreter-reported UB becomes a
  poison constant. Unknown operands are represented by `none`.
-/
def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : FoldDecision :=
  if opType.isConstantLike then .noFold else
  OpCode.foldsTo opType properties resultTypes constOperands

/--
  Read-only convenience wrapper around `foldDecision` for an existing operation.
  The supplied constant array remains explicit so SCCP can provide constants
  inferred from lattice facts rather than only constants materialized in the IR.
-/
def foldDecisionForOp (op : OperationPtr)
    (ctx : WfIRContext OpCode) (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : FoldDecision :=
  if constOperands.size ≠ op.getNumOperands ctx.raw opInBounds then
    .noFold
  else
    let opType := op.getOpType ctx.raw opInBounds
    foldDecision opType
      (op.getProperties ctx.raw opType opInBounds (by grind))
      (op.getResultTypes ctx.raw opInBounds) constOperands

end Veir
