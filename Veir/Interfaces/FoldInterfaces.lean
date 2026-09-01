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
  match foldEvaluate opType properties resultTypes values with
  | .fail => none
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
Try to fold an operation and materialize its replacement values. The return
values distinguish three outcomes:
* `some (rewriter, some results)` - the fold succeeded
* `some (rewriter, none)` - the operation did not fold, or the dialect declined
  to materialize one of its constants
* `none` - a hard failure indicating some sort of serious problem
-/
private def PatternRewriter.tryFold! (rewriter : PatternRewriter OpCode) (opType : OpCode)
    (properties : propertiesOf opType) (resultTypes : Array TypeAttr)
    (operands : Array ValuePtr) (insertionPoint : InsertPoint) :
    Option (PatternRewriter OpCode × Option (Array ValuePtr)) := do
  let some decision := opType.foldsTo properties resultTypes
      (operands.map (ValuePtr.constantValue · rewriter.ctx.raw))
    | return (rewriter, none)
  let some plan := decision.zipIdx.mapM fun (foldResult, index) =>
      match foldResult with
      | .useOperand j => some (Sum.inl operands[j]! : ValuePtr ⊕ Materialized OpCode)
      | .useConstant value =>
        (Sum.inr ·) <$> opType.materializeConstant value resultTypes[index]!
    | return (rewriter, none)
  let mut rewriter := rewriter
  let mut results : Array ValuePtr := #[]
  for (step, index) in plan.zipIdx do
    match step with
    | .inl operand => results := results.push operand
    | .inr ⟨constOpType, constProperties⟩ =>
      let (newRewriter, constantOp) ← rewriter.createOp! constOpType #[resultTypes[index]!]
        #[] #[] #[] constProperties (some insertionPoint)
      rewriter := newRewriter
      results := results.push (constantOp.getResult 0)
  return (rewriter, some results)

/--
Replace every result of a foldable operation with an operand or a materialized
constant, and erase it. Operations that do not fold, and constants that the
dialect declines to represent, leave the IR alone.
-/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  let opType := op.getOpType rewriter.ctx.raw opInBounds
  let resultTypes := op.getResultTypes rewriter.ctx.raw opInBounds
  let properties := op.getProperties rewriter.ctx.raw opType opInBounds (by grind)
  let (newRewriter, replacements) ←
    rewriter.tryFold! opType properties resultTypes operands (.before op)
  let some replacements := replacements | return newRewriter
  let mut rewriter := newRewriter
  for (replacement, index) in replacements.zipIdx do
    rewriter := rewriter.replaceValue! (op.getResult index) replacement
  return rewriter.eraseOp! op

/--
Create an operation, but only if the supplied operands don't allow it to fold.
-/
def PatternRewriter.createOrFold! (rewriter : PatternRewriter OpCode) (opType : OpCode)
    (resultTypes : Array TypeAttr) (operands : Array ValuePtr)
    (blockOperands : Array BlockPtr) (regions : Array RegionPtr)
    (properties : propertiesOf opType) (insertionPoint : InsertPoint) :
    Option (PatternRewriter OpCode × Array ValuePtr) := do
  let (rewriter, results) ←
    rewriter.tryFold! opType properties resultTypes operands insertionPoint
  match results with
  | some results => return (rewriter, results)
  | none =>
    let (rewriter, op) ← rewriter.createOp! opType resultTypes operands blockOperands regions
      properties (some insertionPoint)
    return (rewriter, op.getResults! rewriter.ctx.raw)

end Veir
