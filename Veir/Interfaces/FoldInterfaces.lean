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

/-- The result of an attempt to fold; failure is returned out of band.
    For operations that return multiple results, we need to return an
    array of these. -/
inductive FoldResult where
  /-- Use operand `j` of the folded operation in place of this result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of this result. -/
  | useConstant (rv : RuntimeValue)

/--
  The outcome of folding an operation: one `FoldResult` per result of the
  operation, in result order. An operation folds entirely or not at all, so a
  decision has exactly as many entries as the operation has results.
-/
abbrev FoldDecision := Array FoldResult

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its constant-defined operands (`constOperands[i] =
  some rv` iff operand `i` is known to hold the constant `rv`).
-/
def OpCode.foldsTo (opType : OpCode) (properties : propertiesOf opType)
    (resultTypes : Array TypeAttr) (constOperands : Array (Option RuntimeValue))
    : Option FoldDecision := do
  guard (!opType.isConstantLike)
  guard (!resultTypes.isEmpty)
  let values ← constOperands.mapM id
  match ← (foldEvaluate opType properties resultTypes values : Option (UBOr _)) with
  | .ok results =>
    guard (RuntimeValue.ArrayConforms results resultTypes)
    return results.map .useConstant
  | .ub =>
    let poison ← resultTypes.mapM RuntimeValue.getPoisonForType
    guard (poison.size = resultTypes.size)
    return poison.map .useConstant

/--
  A fold decision has one entry per result of the operation it was computed
  for.
-/
theorem OpCode.foldsTo_size {opType : OpCode} {properties : propertiesOf opType}
    {resultTypes : Array TypeAttr} {constOperands : Array (Option RuntimeValue)}
    {decision : FoldDecision} :
    OpCode.foldsTo opType properties resultTypes constOperands = some decision →
    decision.size = resultTypes.size := by
  intro h
  simp only [OpCode.foldsTo, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    guard, RuntimeValue.ArrayConforms] at h
  obtain ⟨-, -, -, -, -, -, outcome, -, h⟩ := h
  split at h
  · -- The interpreter produced one value per result type.
    split at h
    · simp at h
      grind [Array.size_map]
    · exact absurd h (by simp [failure])
  · -- Undefined behaviour: one poison value per result type.
    simp only [Option.bind_eq_some_iff] at h
    obtain ⟨poison, -, h⟩ := h
    split at h
    · simp at h
      grind [Array.size_map]
    · exact absurd h (by simp [failure])

/--
  Convenience wrapper around `OpCode.foldsTo`.
-/
def OperationPtr.foldsTo (op : OperationPtr)
    (ctx : WfIRContext OpCode) (opInBounds : op.InBounds ctx.raw)
    (constOperands : Array (Option RuntimeValue)) : Option FoldDecision := do
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
  Whether every entry of `decision` can be put in the IR: operand indices are
  in range, and every constant is one that the dialect of `foldingOpType` knows
  how to materialize at the corresponding result type. Folding checks this
  before creating anything, so that a fold either happens for every result or
  does not happen at all.
-/
def FoldDecision.isApplicable (decision : FoldDecision) (foldingOpType : OpCode)
    (operands : Array ValuePtr) (resultTypes : Array TypeAttr) : Bool :=
  decision.size == resultTypes.size &&
  decision.zipIdx.all fun (foldResult, index) =>
    match foldResult with
    | .useOperand j => j < operands.size
    | .useConstant value =>
      match resultTypes[index]? with
      | some resultType => (foldingOpType.materializeConstant value resultType).isSome
      | none => false

/--
Replace every result of a foldable operation with an operand or a materialized
constant, and erase it. Operations that do not fold, and folds that cannot be
materialized, leave the IR alone.
-/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  let constantOperands := operands.map (ValuePtr.constantValue · rewriter.ctx.raw)
  let some decision := op.foldsTo rewriter.ctx opInBounds constantOperands
    | return rewriter
  let opType := op.getOpType rewriter.ctx.raw opInBounds
  let resultTypes := op.getResultTypes rewriter.ctx.raw opInBounds
  -- The folded operation is erased below, and an operation with regions cannot
  -- be. No operation that folds has regions today, since the interpreter does
  -- not evaluate them.
  if op.getNumRegions rewriter.ctx.raw opInBounds ≠ 0 then return rewriter
  -- A decision for an operation with no results would erase it without
  -- replacing anything, which is DCE's business. `foldsTo` never produces one.
  if resultTypes.isEmpty then return rewriter
  if !decision.isApplicable opType operands resultTypes then return rewriter
  let mut rewriter := rewriter
  for (foldResult, index) in decision.zipIdx do
    match foldResult with
    | .useOperand j =>
      -- `isApplicable` checked the index, so this and the two failures below
      -- are inconsistencies rather than folds that declined to happen.
      let some replacement := operands[j]? | none
      rewriter := rewriter.replaceValue! (op.getResult index) replacement
    | .useConstant value =>
      let some resultType := resultTypes[index]? | none
      let some (newRewriter, some constantOp) :=
        rewriter.materializeConstant! opType value resultType (.before op) | none
      rewriter := newRewriter.replaceValue! (op.getResult index) (constantOp.getResult 0)
  -- Every result has been replaced, so the operation is dead.
  return rewriter.eraseOp! op

end Veir
