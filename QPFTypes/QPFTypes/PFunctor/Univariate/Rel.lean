/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import QPFTypes.PFunctor.Univariate.Basic

/-!
# Lifting of relations on polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
-/
@[expose] public section

namespace QPFTypes

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

namespace PFunctor

variable {P : PFunctor.{uA, uB}}

/-- `Liftp p x` asserts that every element in `x` satisfies `p`. -/
def Liftp {α : Type u} (p : α → Prop) (x : P α) : Prop :=
  ∃ u : P { a // p a }, P.map Subtype.val u = x

/-- `Liftr r x y` asserts that every pair of corresponding elements in `x` and `y` is related
by `r`. -/
def Liftr {α : Type u} (r : α → α → Prop) (x y : P α) : Prop :=
  ∃ u : P { p : α × α // r p.1 p.2 },
    P.map (Prod.fst ∘ Subtype.val) u = x ∧ P.map (Prod.snd ∘ Subtype.val) u = y

/-- `supp x` is the set of elements that appear in `x`, as a predicate on `α`. -/
def supp {α : Type u} (x : P α) : α → Prop :=
  fun a => ∀ p, Liftp p x → p a

theorem liftp_iff {α : Type u} (p : α → Prop) (x : P α) :
    Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy, h]; rfl
  rintro ⟨a, f, xeq, pf⟩
  exact ⟨⟨a, fun i => ⟨f i, pf i⟩⟩, by rw [xeq]; rfl⟩

theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    Liftp p (⟨a, f⟩ : P α) ↔ ∀ i, p (f i) := by
  simp only [liftp_iff]
  constructor
  · rintro ⟨a', f', heq, h'⟩
    cases heq; exact h'
  intro h
  exact ⟨a, f, rfl, h⟩

theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    exact ⟨a, fun i => (f i).val.fst, fun i => (f i).val.snd,
      by rw [← xeq, h]; rfl,
      by rw [← yeq, h]; rfl,
      fun i => (f i).property⟩
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩,
    by rw [xeq]; rfl,
    by rw [yeq]; rfl⟩

/-- The support of `⟨a, f⟩` is exactly the range of `f`. -/
theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
    supp (⟨a, f⟩ : P α) = fun x => ∃ i, f i = x := by
  funext x
  apply propext
  simp only [supp]
  constructor
  · intro h
    apply h (fun x => ∃ i, f i = x)
    rw [liftp_iff']
    intro i; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    intro p hp
    rw [liftp_iff'] at hp
    exact hp i

end PFunctor

