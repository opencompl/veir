module

public import Veir.Interpreter.Refinement.Basic

/-!
# Local correctness of dialect fold tables

These contracts concern the decisions returned by `HasOpInfo.tryFold`. They do
not concern constant materialization, the folding driver, or rewriting the IR.
Operand and result types describe a single operation signature; entry proofs
state the signatures they support explicitly.
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

/-- A successful interpretation has no memory or control-flow effect, and its
results are refined by the replacements. UB permits any replacements, but an
interpreter failure never establishes correctness. -/
@[expose]
def Refines (source : Interp (Array RuntimeValue × MemoryState × Option ControlFlowAction))
    (replacements : Array RuntimeValue) (initialMemory : MemoryState) : Prop :=
  match source with
  | .fail => False
  | .ub => True
  | .ok (results, memory, action) =>
    results ⊒ replacements ∧ memory = initialMemory ∧ action = none

/-- Correctness of every successful table lookup at the given operation signature.

Typing is required independently of execution, including when the source has UB.
Semantic correctness quantifies over all well-typed completions of the known
operands, all memories, successor arrays, and data layouts. It uses the operation
interpreter directly, so it does not rely on the driver's poison handling or
evaluation fallback. Returning `none` creates no obligation.
-/
@[expose]
def CorrectAt (op : OpCode) (properties : propertiesOf op)
    (operandTypes resultTypes : Array TypeAttr) : Prop :=
  ∀ known decisions, InputsConform known operandTypes →
    HasOpInfo.tryFold op properties resultTypes known = some decisions →
    FoldDecision.HasTypes decisions operandTypes resultTypes ∧
    ∀ operands, RuntimeValue.ArrayConforms operands operandTypes → Agrees known operands →
      ∀ memory successors layout,
        ∃ replacements, FoldDecision.resolveAll decisions operands = some replacements ∧
          Refines (interpretOp' op properties resultTypes operands successors memory layout)
            replacements memory

end FoldTable
end Veir
