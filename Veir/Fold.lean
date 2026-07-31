module

public import Veir.Interfaces.ConstantLikeInterfaces
public import Veir.Interpreter.Basic
public import Veir.Interpreter.Evaluate

/-!
  # Constant folding decisions

  An operation whose operands are all known constants can be queried through
  `OpCode.foldsTo`, which resolves the fold by running the interpreter. There
  are no per-dialect fold tables here: an operation with any unknown operand
  never folds, however trivial the algebraic identity would be. This module
  never mutates the IR or materializes constants.
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

/-- Construct a poison decision for a supported result type. -/
private def poisonDecision (resultTypes : Array TypeAttr) : FoldDecision :=
  match resultTypes[0]? with
  | some resultType =>
    match resultType.val with
    | .integerType intTy => .useConstant (.int intTy.bitwidth .poison)
    | _ => .noFold
  | none => .noFold

/-- Return a constant decision only when `rv` conforms to the sole result type. -/
private def conformingConstantDecision
    (resultTypes : Array TypeAttr) (rv : RuntimeValue) : FoldDecision :=
  match resultTypes.toList with
  | [resultType] =>
    if rv.Conforms resultType then .useConstant rv else .noFold
  | _ => .noFold

/-- Resolve all-constant folding with the interpreter. -/
private def evaluatedFoldDecision (opCode : OpCode)
    (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (values : Array RuntimeValue) :
    FoldDecision :=
  match (foldEvaluate opCode properties resultTypes values : Option (UBOr _)) with
  | none => .noFold
  | some (.ok results) =>
    match results.toList with
    | [result] => conformingConstantDecision resultTypes result
    | _ => .noFold
  | some .ub => poisonDecision resultTypes

/--
  Query whether an operation folds, given its result types and the values of
  its constant-defined operands (`constOperands[i] = some rv` iff operand `i`
  is defined by a constant-like operation with value `rv`).

  Every operand must be known: the interpreter is the only source of fold
  decisions, so a single `none` yields `.noFold`.
-/
def OpCode.foldsTo (opCode : OpCode) (properties : HasOpInfo.propertiesOf opCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue)) :
    FoldDecision :=
  if resultTypes.size ≠ 1 then .noFold else
  match constOperands.mapM id with
  | none => .noFold
  | some values => evaluatedFoldDecision opCode properties resultTypes values

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
