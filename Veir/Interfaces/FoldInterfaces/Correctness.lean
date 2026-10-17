module

public import Veir.Interpreter.Refinement.Basic
public import Veir.Verifier

/-!
# Local correctness of dialect fold tables

These contracts concern the decisions returned by `HasOpInfo.tryFold`. They do
not concern constant materialization, the folding driver, or rewriting the IR.
The operation's signature and properties come from a verified operation in its
IR context.
-/

public section

namespace Veir

/-- A replacement has the result's exact type, and any operand index is in range. -/
@[expose]
def FoldDecision.HasType (operandTypes : Array TypeAttr) (decision : FoldDecision)
    (resultType : TypeAttr) : Prop :=
  match decision with
  | .useOperand j => operandTypes[j]? = some resultType
  | .useConstant value => value.Conforms resultType

/-- There is one well-typed replacement for each result, in result order. -/
@[expose]
def FoldDecision.HasTypes (decisions : Array FoldDecision)
    (operandTypes resultTypes : Array TypeAttr) : Prop :=
  decisions.size = resultTypes.size ∧
    ∀ i (h : i < decisions.size), HasType operandTypes decisions[i] resultTypes[i]!

/-- Interpret a decision without creating any IR. Invalid operand indices fail. -/
@[expose]
def FoldDecision.resolve (operands : Array RuntimeValue) : FoldDecision → Option RuntimeValue
  | .useOperand j => operands[j]?
  | .useConstant value => some value

/-- Interpret all decisions, preserving their order and checking every operand index. -/
@[expose]
def FoldDecision.resolveAll (decisions : Array FoldDecision) (operands : Array RuntimeValue) :
    Option (Array RuntimeValue) :=
  List.toArray <$> decisions.toList.mapM (FoldDecision.resolve operands)

namespace FoldTable

/-- Known operands have the declared types; unknown operands impose no value constraint.
The arrays must have the same length. -/
@[expose]
def InputsConform (known : Array (Option RuntimeValue)) (operandTypes : Array TypeAttr) : Prop :=
  known.size = operandTypes.size ∧
    ∀ i, i < known.size → ∀ v, known[i]! = some v → v.Conforms operandTypes[i]!

/-- A runtime assignment agrees with every known operand. Unknown operands may
be any conforming value, including poison. The arrays must have the same length. -/
@[expose]
def Agrees (known : Array (Option RuntimeValue)) (operands : Array RuntimeValue) : Prop :=
  known.size = operands.size ∧
    ∀ i, i < known.size → ∀ v, known[i]! = some v → operands[i]! = v

/-- Correctness of every successful table lookup for a verified operation.

Typing is required independently of execution, including when the source has UB.
Semantic correctness quantifies over all well-typed completions of the known
operands, all memories, and data layouts, using the operation's actual successors.
Interpreter failure is excluded explicitly for every layout. It uses the operation
interpreter directly, so it does not rely on the driver's poison handling or
evaluation fallback. Returning `none` creates no obligation.
-/
structure CorrectAt (ctx : WfIRContext OpCode) (op : OperationPtr)
    {opIn : op.InBounds ctx.raw} (_verified : op.Verified ctx opIn) : Prop where
  /-- Every successful lookup returns one replacement of the corresponding type per result. -/
  hasTypes :
    ∀ known decisions, InputsConform known (op.getOperandTypes! ctx.raw) →
      HasOpInfo.tryFold (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) known = some decisions →
      FoldDecision.HasTypes decisions (op.getOperandTypes! ctx.raw) (op.getResultTypes! ctx.raw)
  /-- The replacements refine the operation for every well-typed completion of the known operands. -/
  preservesSemantics :
    ∀ known decisions,
      HasOpInfo.tryFold (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) known = some decisions →
      ∀ operands, RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
        Agrees known operands → ∀ memory layout,
          ∃ replacements, FoldDecision.resolveAll decisions operands = some replacements ∧
            (op.interpret ctx.raw operands memory layout).isFail = false ∧
            Interp.isRefinedBy OperationResult.isRefinedBy
              (op.interpret ctx.raw operands memory layout) (.ok (replacements, memory, none))

end FoldTable
end Veir
