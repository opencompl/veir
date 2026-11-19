module

public import Veir.Verifier

/-!
# Local correctness of dialect fold tables.
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

/-- Typing a single replacement reduces to typing its decision. -/
@[simp, grind =]
theorem FoldDecision.hasTypes_singleton :
    HasTypes #[decision] operands #[type] ↔ HasType operands decision type := by
  simp [HasTypes]

/-- Typing two replacements reduces to their individual typing obligations. -/
@[simp, grind =]
theorem FoldDecision.hasTypes_pair :
    HasTypes #[a, b] operands #[ta, tb] ↔
      HasType operands a ta ∧ HasType operands b tb := by
  simp [HasTypes, Nat.forall_lt_succ_left']

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

/-- Correctness of every successful table lookup, assuming the operation is verified.
Basically, we just insist that interpretation succeeds in an arbitrary memory layout,
and produces a result that is refined by whatever is in the table. -/
structure CorrectAt (ctx : WfIRContext OpCode) (op : OperationPtr) : Prop where
  /-- Every successful lookup returns one replacement of the corresponding type per result. -/
  hasTypes {opIn : op.InBounds ctx.raw} : op.Verified ctx opIn →
    ∀ known decisions, InputsConform known (op.getOperandTypes! ctx.raw) →
      HasOpInfo.tryFold (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) known = some decisions →
      FoldDecision.HasTypes decisions (op.getOperandTypes! ctx.raw) (op.getResultTypes! ctx.raw)
  /-- The operation does not fail, and the replacements refine it, for every well-typed
  completion of the known operands. -/
  preservesSemantics {opIn : op.InBounds ctx.raw} : op.Verified ctx opIn →
    ∀ known decisions,
      HasOpInfo.tryFold (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) known = some decisions →
      ∀ operands, RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw) →
        Agrees known operands → ∀ memory layout,
          (op.interpret ctx.raw operands memory layout).isFail = false ∧
          ∃ replacements, FoldDecision.resolveAll decisions operands = some replacements ∧
            Interp.isRefinedBy OperationResult.isRefinedBy
              (op.interpret ctx.raw operands memory layout) (.ok (replacements, memory, none))

/-- Prove both obligations under a single verification hypothesis, so that facts
derived from the verifier are available to each of them. -/
theorem CorrectAt.of_verified {ctx : WfIRContext OpCode} {op : OperationPtr}
    (h : ∀ opIn, op.Verified ctx opIn → CorrectAt ctx op) : CorrectAt ctx op where
  hasTypes verified := (h _ verified).hasTypes verified
  preservesSemantics verified := (h _ verified).preservesSemantics verified

/-- An operation whose opcode never folds is trivially correct. -/
theorem CorrectAt.of_tryFold_none {ctx : WfIRContext OpCode} {op : OperationPtr}
    (h : ∀ known, HasOpInfo.tryFold (op.getOpType! ctx.raw)
      (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
      (op.getResultTypes! ctx.raw) known = none) :
    CorrectAt ctx op where
  hasTypes _ known decisions _ hFold := by simp [h] at hFold
  preservesSemantics _ known decisions hFold := by simp [h] at hFold

/-- Reduce an integer binary fold with a known right operand to its typing and
value semantics. The lookup describes which decisions are returned; this helper
handles width agreement and every consistent runtime completion. The right
operand may depend on its width, for example zero or all ones. -/
theorem correctAt_int_rhs
    {ctx : WfIRContext OpCode} {op : OperationPtr} {type : IntegerType}
    (operandTypes : op.getOperandTypes! ctx.raw = #[(type : TypeAttr), (type : TypeAttr)])
    (rhs : (width : Nat) → Data.LLVM.Int width)
    (lookup : ∀ known results,
      HasOpInfo.tryFold (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) known = some results →
      ∃ left width, known = #[left, some (.int width (rhs width))] ∧ results = decisions)
    (typed : FoldDecision.HasTypes decisions
      (op.getOperandTypes! ctx.raw) (op.getResultTypes! ctx.raw))
    (evaluate : ∀ lhs memory layout,
      let operands := #[.int type.bitwidth lhs, .int type.bitwidth (rhs type.bitwidth)]
      (op.interpret ctx.raw operands memory layout).isFail = false ∧
      ∃ replacements,
        FoldDecision.resolveAll decisions operands = some replacements ∧
        Interp.isRefinedBy OperationResult.isRefinedBy
          (op.interpret ctx.raw operands memory layout)
          (.ok (replacements, memory, none))) :
    CorrectAt ctx op where
  hasTypes _ known results _ hFold := by
    obtain ⟨_, _, _, rfl⟩ := lookup known results hFold
    exact typed
  preservesSemantics _ known results hFold operands hOperands hAgree memory layout := by
    obtain ⟨left, width, rfl, rfl⟩ := lookup known results hFold
    obtain ⟨lhs, actualRhs, rfl⟩ := by simpa [operandTypes] using hOperands
    cases hAgree.2 1 (by simp) _ rfl
    exact evaluate lhs memory layout

end FoldTable
end Veir
