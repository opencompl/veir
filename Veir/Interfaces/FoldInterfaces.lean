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

inductive FoldDecision where
  /-- Use operand `j` in place of the result. -/
  | useOperand (j : Nat)
  /-- Use the runtime constant `rv` in place of the result. -/
  | useConstant (rv : RuntimeValue)

/--
  Decide whether an operation folds, given its opcode, properties, result
  types, and the values of its constant-defined operands (`constOperands[i] =
  some rv` iff operand `i` is known to hold the constant `rv`).
-/
def OpCode.foldsTo (opType : OpCode) (properties : propertiesOf opType)
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
  | .ub => return .useConstant (← RuntimeValue.getPoisonForType resultType)

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

/-- Replace a foldable operation with an operand or a materialized constant. -/
def foldOperation (rewriter : PatternRewriter OpCode) (op : OperationPtr)
    (opInBounds : op.InBounds rewriter.ctx.raw) : Option (PatternRewriter OpCode) := do
  let operands := op.getOperands rewriter.ctx.raw opInBounds
  let constantOperands := operands.map (ValuePtr.constantValue · rewriter.ctx.raw)
  match op.foldsTo rewriter.ctx opInBounds constantOperands with
  | none => return rewriter
  | some (.useOperand index) =>
    let replacement ← operands[index]?
    let rewriter := rewriter.replaceValue! (op.getResult 0) replacement
    return rewriter.eraseOp! op
  | some (.useConstant value) =>
    let resultType ← (op.getResultTypes rewriter.ctx.raw opInBounds)[0]?
    match rewriter.materializeConstant! (op.getOpType rewriter.ctx.raw opInBounds)
        value resultType (.before op) with
    | none => none
    | some (rewriter, none) => some rewriter
    | some (rewriter, some constantOp) => some (rewriter.replaceOp! op constantOp)

end Veir
