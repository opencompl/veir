module

public import Veir.Fold.Basic
public import Veir.Interfaces.ConstantLikeInterfaces
public import Veir.Interpreter.Evaluate

/-!
  # Constant folding decisions

  Each dialect supplies its partial fold table through
  `HasDialectOpInfo.foldsTo`. This module adds generic validation and
  interpreter-backed evaluation for the all-constant case. It never mutates
  the IR or materializes constants.
-/

public section

namespace Veir

/-- Return a constant decision only when `rv` conforms to the sole result type. -/
private def conformingConstantDecision
    (resultTypes : Array TypeAttr) (rv : RuntimeValue) : FoldDecision :=
  match resultTypes.toList with
  | [resultType] =>
    if rv.Conforms resultType then .useConstant rv else .noFold
  | _ => .noFold

/-- Resolve generic all-constant folding with the interpreter. -/
private def evaluatedFoldDecision (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  let values := constOperands.map (·.get!)
  match (foldEvaluate opCode properties resultTypes values : Option (UBOr _)) with
  | none => .noFold
  | some (.ok results) =>
    match results.toList with
    | [result] => conformingConstantDecision resultTypes result
    | _ => .noFold
  | some .ub => Fold.poisonDecision resultTypes

/-- Reject malformed operand and constant decisions from dialect fold tables. -/
private def validateFoldDecision (resultTypes : Array TypeAttr)
    (constOperands : Array (Option RuntimeValue)) (decision : FoldDecision) :
    FoldDecision :=
  match decision with
  | .useOperand j =>
    if j < constOperands.size then .useOperand j else .noFold
  | .useConstant rv => conformingConstantDecision resultTypes rv
  | .noFold => .noFold

/--
  Query whether an operation folds, given its result types and the values of
  its constant-defined operands (`constOperands[i] = some rv` iff operand `i`
  is defined by a constant-like operation with value `rv`).
-/
def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  if resultTypes.size ≠ 1 then .noFold else
  let tableDecision := validateFoldDecision resultTypes constOperands <|
    HasDialectOpInfo.foldsTo opCode properties resultTypes constOperands
  match tableDecision with
  | .useOperand j => .useOperand j
  | .useConstant rv => .useConstant rv
  | .noFold =>
    if constOperands.all (·.isSome) then
      evaluatedFoldDecision opCode properties resultTypes constOperands
    else
      .noFold

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
