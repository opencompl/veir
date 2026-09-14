module

public import Veir.Interfaces.FoldInterfaces.Correctness
public import Veir.Interpreter.Refinement.Lemmas

import all Veir.IR.Attribute

/-! Helpers for proving local fold-table correctness. -/

public section

namespace Veir
open Data

/-- Recover the integer operands from their declared widths. -/
theorem RuntimeValue.ArrayConforms.int_pair
    (h : RuntimeValue.ArrayConforms operands
      #[(IntegerType.mk w₁ : TypeAttr), (IntegerType.mk w₂ : TypeAttr)]) :
    ∃ lhs rhs, operands = #[.int w₁ lhs, .int w₂ rhs] := by
  have hs : operands.size = 2 := h.1
  have h0 := h.2 0 (by omega)
  have h1 := h.2 1 (by omega)
  simp at h0 h1
  obtain ⟨lhs, hl⟩ := RuntimeValue.Conforms.integerType h0
  obtain ⟨rhs, hr⟩ := RuntimeValue.Conforms.integerType h1
  refine ⟨lhs, rhs, ?_⟩
  apply Array.ext <;> grind

/-- Recover a single register operand, regardless of its allocation. -/
theorem RuntimeValue.ArrayConforms.reg_single {type : RegisterType}
    (h : RuntimeValue.ArrayConforms operands #[(type : TypeAttr)]) :
    ∃ value, operands = #[.reg value] := by
  obtain ⟨value, rfl⟩ := Array.size_eq_one_iff.mp h.1
  have hv := h.2 0 (by simp)
  simp at hv
  obtain ⟨reg, rfl⟩ := RuntimeValue.Conforms.registerType hv
  exact ⟨reg, rfl⟩

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

/-- Reduce an integer binary fold with a known right operand to its typing and
value semantics. The lookup describes which decisions are returned; this helper
handles width agreement and every consistent runtime completion. The right
operand may depend on its width, for example zero or all ones. -/
theorem FoldTable.correctAt_int_rhs
    (rhs : (width : Nat) → LLVM.Int width)
    (lookup : ∀ known results,
      HasOpInfo.tryFold op properties resultTypes known = some results →
      ∃ left width, known = #[left, some (.int width (rhs width))] ∧ results = decisions)
    (typed : FoldDecision.HasTypes decisions
      #[(IntegerType.mk w : TypeAttr), (IntegerType.mk w : TypeAttr)] resultTypes)
    (evaluate : ∀ lhs memory successors layout,
      ∃ replacements,
        FoldDecision.resolveAll decisions #[.int w lhs, .int w (rhs w)] = some replacements ∧
        Refines (interpretOp' op properties resultTypes
          #[.int w lhs, .int w (rhs w)] successors memory layout) replacements memory) :
    CorrectAt op properties
      #[(IntegerType.mk w : TypeAttr), (IntegerType.mk w : TypeAttr)] resultTypes := by
  intro known results hKnown hFold
  obtain ⟨left, width, rfl, rfl⟩ := lookup known results hFold
  have hw := hKnown.2 1 (by simp) (.int width (rhs width)) (by simp)
  simp [RuntimeValue.Conforms, Attribute.asType] at hw
  subst width
  refine ⟨typed, ?_⟩
  intro operands hOperands hAgree memory successors layout
  obtain ⟨lhs, actualRhs, rfl⟩ := hOperands.int_pair
  have hr := hAgree.2 1 (by simp) (.int w (rhs w)) (by simp)
  simp at hr
  subst actualRhs
  exact evaluate lhs memory successors layout

end Veir
