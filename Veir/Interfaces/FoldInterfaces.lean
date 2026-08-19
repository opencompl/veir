module

public import Veir.Interfaces.ConstantLikeInterfaces
public import Veir.Interpreter.Basic
public import Veir.Interpreter.Evaluate
public import Veir.PatternRewriter.Basic

/-!
  # Constant folding decision interface

  This file is the public entry point for deciding whether operations fold,
  for materializing folded constants in the IR, and for the rewrite pattern
  that applies a fold to an operation.
-/

public section

namespace Veir

/-- What one result of a folded operation is replaced with; failure to fold is
    returned out of band. Folding an operation yields an array of these, one per
    result and in result order: an operation folds entirely or not at all, so
    the array has exactly as many entries as the operation has results. -/
inductive FoldResult where
  /-- Use operand `j` of the folded operation in place of this result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of this result. -/
  | useConstant (rv : RuntimeValue)

/-- Every result of the operation folds to poison, for the result types that
    have a poison representation. -/
private def allResultsPoison (resultTypes : Array TypeAttr) : Option (Array FoldResult) := do
  return (← resultTypes.mapM RuntimeValue.getPoisonForType).map .useConstant

/--
  Fold an operation by evaluating it, which requires every operand to be known.
  Evaluation that triggers UB folds to poison.
-/
private def foldByEvaluation (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : Option (Array FoldResult) := do
  let values ← constOperands.mapM id
  match ← (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
  | .ok results => return results.map .useConstant
  | .ub => allResultsPoison resultTypes

/--
  Fold an operation that propagates poison and has a wholly poisoned operand.
  Unlike evaluation, this fires whether or not the remaining operands are known.
-/
private def foldPoisonedOperand (opType : OpCode)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : Option (Array FoldResult) := do
  guard opType.propagatesPoison
  guard (constOperands.any fun
    | some value => value.isPoison
    | none => false)
  allResultsPoison resultTypes

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its constant-defined operands (`constOperands[i] =
  some rv` iff operand `i` is known to hold the constant `rv`).
-/
def OpCode.foldsTo (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : Option (Array FoldResult) := do
  guard (!opType.isConstantLike)
  foldByEvaluation opType properties resultTypes constOperands <|>
    foldPoisonedOperand opType resultTypes constOperands

/--
  Convenience wrapper around `OpCode.foldsTo`.
-/
def OperationPtr.foldsTo (op : OperationPtr)
    (ctx : WfIRContext OpCode) (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : Option (Array FoldResult) := do
  guard (constOperands.size = op.getNumOperands ctx.raw opInBounds)
  let opType := op.getOpType ctx.raw opInBounds
  OpCode.foldsTo opType
    (op.getProperties ctx.raw opType opInBounds (by grind))
    (op.getResultTypes ctx.raw opInBounds) constOperands

/--
Materialize `value` using the materialization hook of `foldingOpType`'s dialect.
The hook may select a constant-like operation from another dialect.

The return values signal two different failure modes:
* `some (rewriter, none)` - the constant cannot be materialized, this means the
   rewrite doesn't happen but there's no cause for concern
* `none` - the operation could not be created; in this case the entire pass
   should generate a hard failure
-/
def PatternRewriter.materializeConstant! (rewriter : PatternRewriter OpCode)
    (foldingOpType : OpCode) (value : RuntimeValue) (resultType : TypeAttr)
    (insertionPoint : InsertPoint) :
    Option (PatternRewriter OpCode × Option OperationPtr) := do
  let some ⟨opType, properties⟩ := foldingOpType.materializeConstant value resultType
    | return (rewriter, none)
  let (rewriter, op) ← rewriter.createOp! opType #[resultType] #[] #[] #[] properties
    (some insertionPoint)
  return (rewriter, some op)

/--
Replace every result of a foldable operation with an operand or a materialized
constant, and erase it. Operations that do not fold, and constants that the
dialect declines to represent, leave the IR alone.
-/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  let constantOperands := operands.map (ValuePtr.constantValue · rewriter.ctx.raw)
  let some decision := op.foldsTo rewriter.ctx opInBounds constantOperands
    | return rewriter
  let opType := op.getOpType rewriter.ctx.raw opInBounds
  let resultTypes := op.getResultTypes rewriter.ctx.raw opInBounds
  -- Collect a replacement for every result before redirecting any of them
  let mut rewriter := rewriter
  let mut replacements : Array ValuePtr := #[]
  for (foldResult, index) in decision.zipIdx do
    match foldResult with
    | .useOperand j => replacements := replacements.push operands[j]!
    | .useConstant value =>
      let (newRewriter, materialized) ←
        rewriter.materializeConstant! opType value resultTypes[index]! (.before op)
      let some constantOp := materialized | return rewriter
      rewriter := newRewriter
      replacements := replacements.push (constantOp.getResult 0)
  for (replacement, index) in replacements.zipIdx do
    rewriter := rewriter.replaceValue! (op.getResult index) replacement
  return rewriter.eraseOp! op

end Veir
