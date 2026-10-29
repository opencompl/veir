module

public import Veir.Interpreter.Refinement.Basic

/-!
# Soundness of dialect fold tables

A fold table, `HasOpInfo.tryFold`, decides that an operation folds given only
some of its operands. It is sound when, for every assignment of runtime values
that agrees with the known operands, the decided replacements refine what the
interpreter computes. This file defines that agreement and resolution, and
lemmas for proving a table sound one entry at a time.
-/

public section

namespace Veir

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

/-- A runtime assignment agrees with every known operand. Unknown operands may
be any value, including poison. The arrays must have the same length. -/
@[expose]
def FoldTable.Agrees (known : Array (Option RuntimeValue)) (operands : Array RuntimeValue) : Prop :=
  known.size = operands.size ∧
    ∀ i, i < known.size → ∀ v, known[i]! = some v → operands[i]! = v

namespace FoldTable

/-- Each operand is unknown or equal to its runtime value. -/
private theorem Agrees.list {l : List (Option RuntimeValue)} {operands : List RuntimeValue}
    (h : Agrees l.toArray operands.toArray) :
    l.length = operands.length ∧ ∀ i (hi : i < l.length) (ho : i < operands.length),
      l[i] = none ∨ l[i] = some operands[i] := by
  obtain ⟨hsize, hval⟩ := h
  simp only [List.size_toArray] at hsize
  refine ⟨hsize, fun i hi ho => ?_⟩
  cases hl : l[i] with
  | none => exact .inl rfl
  | some v =>
    have := hval i (by simpa using hi) v (by simp [hl, hi])
    simp_all

theorem Agrees.single (hAgree : Agrees known operands) (h : known.toList = [x]) :
    ∃ a, operands = #[a] ∧ (x = none ∨ x = some a) := by
  obtain ⟨known⟩ := known
  obtain ⟨operands⟩ := operands
  simp only at h
  subst h
  obtain ⟨hsize, hval⟩ := hAgree.list
  match operands, hsize with
  | [a], _ => exact ⟨a, rfl, by simpa using hval 0 (by simp) (by simp)⟩

theorem Agrees.pair (hAgree : Agrees known operands) (h : known.toList = [x, y]) :
    ∃ a b, operands = #[a, b] ∧ (x = none ∨ x = some a) ∧ (y = none ∨ y = some b) := by
  obtain ⟨known⟩ := known
  obtain ⟨operands⟩ := operands
  simp only at h
  subst h
  obtain ⟨hsize, hval⟩ := hAgree.list
  match operands, hsize with
  | [a, b], _ =>
    exact ⟨a, b, rfl, by simpa using hval 0 (by simp) (by simp),
      by simpa using hval 1 (by simp) (by simp)⟩

theorem Agrees.triple (hAgree : Agrees known operands) (h : known.toList = [x, y, z]) :
    ∃ a b c, operands = #[a, b, c] ∧ (x = none ∨ x = some a) ∧ (y = none ∨ y = some b) ∧
      (z = none ∨ z = some c) := by
  obtain ⟨known⟩ := known
  obtain ⟨operands⟩ := operands
  simp only at h
  subst h
  obtain ⟨hsize, hval⟩ := hAgree.list
  match operands, hsize with
  | [a, b, c], _ =>
    exact ⟨a, b, c, rfl, by simpa using hval 0 (by simp) (by simp),
      by simpa using hval 1 (by simp) (by simp), by simpa using hval 2 (by simp) (by simp)⟩

/-!
Each table entry is a chain of alternatives joined by `<|>`. These lemmas take a
property of the decisions apart along that chain, leaving one obligation per
alternative: that the alternative's decisions are correct when its condition
holds.
-/

theorem orElse_sound {P : Array FoldDecision → Prop} {x y : Option (Array FoldDecision)}
    (hx : ∀ d, x = some d → P d) (hy : ∀ d, y = some d → P d) :
    ∀ d, (x <|> y) = some d → P d := by
  intro d h
  cases x <;> simp_all [HOrElse.hOrElse, OrElse.orElse, Option.orElse]

theorem useOperandIf_sound {P : Array FoldDecision → Prop}
    (h : c = true → P #[.useOperand j]) : ∀ d, FoldDecision.useOperandIf c j = some d → P d := by
  intro d hd
  cases c <;> simp_all [FoldDecision.useOperandIf]

theorem useConstantIf_sound {P : Array FoldDecision → Prop}
    (h : c = true → P #[.useConstant v]) :
    ∀ d, FoldDecision.useConstantIf c v = some d → P d := by
  intro d hd
  cases c <;> simp_all [FoldDecision.useConstantIf]

theorem ite_sound {P : Array FoldDecision → Prop} {x y : Option (Array FoldDecision)}
    (hx : c → ∀ d, x = some d → P d) (hy : ¬c → ∀ d, y = some d → P d) [Decidable c] :
    ∀ d, (if c then x else y) = some d → P d := by
  intro d hd
  by_cases hc : c <;> simp_all

theorem bind_sound {P : Array FoldDecision → Prop} {x : Option α}
    {f : α → Option (Array FoldDecision)} (h : ∀ a, x = some a → ∀ d, f a = some d → P d) :
    ∀ d, (x >>= f) = some d → P d := by
  intro d hd
  cases hx : x <;> simp_all [bind, Option.bind]

theorem some_sound {P : Array FoldDecision → Prop} (h : P d₀) :
    ∀ d, some d₀ = some d → P d := by
  rintro d ⟨⟩
  exact h

theorem none_sound {P : Array FoldDecision → Prop} : ∀ d, (none : Option _) = some d → P d := by
  simp

end FoldTable

end Veir
