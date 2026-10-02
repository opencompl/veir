module

public import Veir.Interfaces.FoldInterfaces.Correctness
public import Veir.Interpreter.Refinement.Lemmas

import all Veir.IR.Attribute
import all Veir.Verifier.Lemmas

/-! Helpers for proving local fold-table correctness. -/

public section

namespace Veir
open Data

/-- Recover the integer operands from their declared widths. -/
theorem RuntimeValue.ArrayConforms.int_pair
    {type₁ type₂ : IntegerType}
    (h : RuntimeValue.ArrayConforms operands
      #[(type₁ : TypeAttr), (type₂ : TypeAttr)]) :
    ∃ lhs rhs, operands = #[.int type₁.bitwidth lhs, .int type₂.bitwidth rhs] := by
  simpa using h

/-- Recover a single register operand, regardless of its allocation. -/
theorem RuntimeValue.ArrayConforms.reg_single {type : RegisterType}
    (h : RuntimeValue.ArrayConforms operands #[(type : TypeAttr)]) :
    ∃ value, operands = #[.reg value] := by
  simpa using h

/-- Typing a single replacement reduces to typing its decision. -/
@[simp]
theorem FoldDecision.hasTypes_singleton :
    HasTypes #[decision] operands #[type] ↔ HasType operands decision type := by
  simp [HasTypes]

/-- Typing two replacements reduces to their individual typing obligations. -/
@[simp]
theorem FoldDecision.hasTypes_pair :
    HasTypes #[a, b] operands #[ta, tb] ↔
      HasType operands a ta ∧ HasType operands b tb := by
  simp [HasTypes, Nat.forall_lt_succ_left']

/-- Refinement of two results is pointwise. -/
@[simp]
theorem RuntimeValue.arrayIsRefinedBy_pair :
    #[a, b] ⊒ #[c, d] ↔ a ⊒ c ∧ b ⊒ d := by
  simp only [arrayIsRefinedBy_cons, arrayIsRefinedBy_nil, and_true]

/-- Recover the complete type arrays of a verified integer binary operation. -/
theorem OperationPtr.IsVerifiedIntegerBinop.types
    {ctx : WfIRContext OpCode} {op : OperationPtr} (h : op.IsVerifiedIntegerBinop ctx) :
    ∃ type : IntegerType,
      op.getOperandTypes! ctx.raw = #[(type : TypeAttr), (type : TypeAttr)] ∧
      op.getResultTypes! ctx.raw = #[(type : TypeAttr)] := by
  obtain ⟨_, _, _, _, type, _, _, _⟩ := h
  refine ⟨type, ?_, ?_⟩ <;> apply Array.ext <;> grind

/-- Reduce an integer binary fold with a known right operand to its typing and
value semantics. The lookup describes which decisions are returned; this helper
handles width agreement and every consistent runtime completion. The right
operand may depend on its width, for example zero or all ones. -/
theorem FoldTable.correctAt_int_rhs
    {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}
    (verified : op.Verified ctx opIn) {type : IntegerType}
    (operandTypes : op.getOperandTypes! ctx.raw = #[(type : TypeAttr), (type : TypeAttr)])
    (rhs : (width : Nat) → LLVM.Int width)
    (lookup : ∀ known results,
      HasOpInfo.tryFold (op.getOpType! ctx.raw)
        (op.getProperties! ctx.raw (op.getOpType! ctx.raw))
        (op.getResultTypes! ctx.raw) known = some results →
      ∃ left width, known = #[left, some (.int width (rhs width))] ∧ results = decisions)
    (typed : FoldDecision.HasTypes decisions
      (op.getOperandTypes! ctx.raw) (op.getResultTypes! ctx.raw))
    (evaluate : ∀ lhs memory layout,
      ∃ replacements,
        FoldDecision.resolveAll decisions
          #[.int type.bitwidth lhs, .int type.bitwidth (rhs type.bitwidth)] = some replacements ∧
        (op.interpret ctx.raw
          #[.int type.bitwidth lhs, .int type.bitwidth (rhs type.bitwidth)] memory layout).isFail = false ∧
        Interp.isRefinedBy OperationResult.isRefinedBy
          (op.interpret ctx.raw
            #[.int type.bitwidth lhs, .int type.bitwidth (rhs type.bitwidth)] memory layout)
          (.ok (replacements, memory, none))) :
    CorrectAt ctx op verified where
  hasTypes known results _ hFold := by
    obtain ⟨_, _, _, rfl⟩ := lookup known results hFold
    exact typed
  preservesSemantics known results hFold operands hOperands hAgree memory layout := by
    obtain ⟨left, width, rfl, rfl⟩ := lookup known results hFold
    rw [operandTypes] at hOperands
    obtain ⟨lhs, actualRhs, rfl⟩ := hOperands.int_pair
    have hr := hAgree.2 1 (by simp) (.int width (rhs width)) (by simp)
    have hw : type.bitwidth = width := by injection hr
    subst width
    simp at hr
    subst actualRhs
    exact evaluate lhs memory layout

end Veir
