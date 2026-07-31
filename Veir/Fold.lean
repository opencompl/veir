module

public import Veir.Interfaces.ConstantLikeInterfaces
public import Veir.Interpreter.Basic
public import Veir.Interpreter.Evaluate

/-!
  # Constant folding decisions
-/

public section

namespace Veir

/--
  The decision of whether and how an operation folds. Folding is currently
  restricted to operations with exactly one result.
-/
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

  Folding requires a single result type and a value for every operand: the
  interpreter is the only source of fold decisions, so a single `none` yields
  `.noFold`.
-/
def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  if !constOperands.all (·.isSome) then .noFold else
  let values := constOperands.map (·.get!)
  match resultTypes.toList with
  | [resultType] =>
    match (foldEvaluate opCode properties #[resultType] values : Option (UBOr _)) with
    | none => .noFold
    | some (.ok results) =>
      -- The interpreter may disagree about arity, so the lone result is checked.
      match results.toList with
      | [result] => if result.Conforms resultType then .useConstant result else .noFold
      | _ => .noFold
    | some .ub =>
      -- UB may be refined by any value; poison is the strongest one available.
      match resultType.val with
      | .integerType intTy => .useConstant (.int intTy.bitwidth .poison)
      | _ => .noFold
  | _ => .noFold

namespace Fold.Impl

def foldDecision (opType : OpCode) (properties : HasOpInfo.propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : FoldDecision :=
  if opType.isConstantLike then .noFold else
  OpCode.foldsTo opType properties resultTypes constOperands

def foldDecisionForOp (op : OperationPtr) (ctx : WfIRContext OpCode)
    (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : FoldDecision :=
  if constOperands.size ≠ op.getNumOperands ctx.raw opInBounds then
    .noFold
  else
    let opType := op.getOpType ctx.raw opInBounds
    foldDecision opType
      (op.getProperties ctx.raw opType opInBounds (by grind))
      (op.getResultTypes ctx.raw opInBounds) constOperands

end Fold.Impl

end Veir
