/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.PFunctor.Multivariate.Basic

/-!
# Relational lifting over multivariate polynomial functors

Often it is useful to enable reasoning about the values stored at each direction of a polynomial functor.
This module provides two methods for this, LiftP and LiftR.
These allow the user to give a family of predicates (respectively relations),
over the values contained in an element of the result of a polynomial functor.
-/
@[expose] public section

namespace QPFTypes.MvPFunctor

open TypeVec

universe u

variable {n m : Nat} (P : MvPFunctor.{u} n)

variable (P : MvPFunctor.{u} n)

/-- `LiftP p x` asserts that every element in `x` satisfies `p`. -/
def LiftP {α : TypeVec n} (p : ∀ i, α i → Prop) (x : P α) : Prop :=
  ∃ u : P (fun i => { a // p i a }), P.map (fun _ => Subtype.val) u = x

/-- `LiftR r x y` asserts that every pair of corresponding elements in `x` and `y` is related
by `r`. -/
def LiftR {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P α) : Prop :=
  ∃ u : P (fun i => { p : α i × α i // r p.1 p.2 }),
    P.map (fun _ t => t.val.1) u = x ∧ P.map (fun _ t => t.val.2) u = y

/-- `supp x i` is the set of `α i` values that appear in `x`, as a predicate. -/
def supp {α : TypeVec n} (x : P α) (i : Fin n) : α i → Prop :=
  fun y => ∀ ⦃p : ∀ i, α i → Prop⦄, LiftP P p x → p i y

variable {P}

theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : P α) :
    LiftP P p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    erw [← hy, h, map_eq]; rfl
  rintro ⟨a, f, xeq, pf⟩
  exact ⟨⟨a, fun i j => ⟨f i j, pf i j⟩⟩, by rw [xeq]; rfl⟩

theorem liftP_iff' {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
    LiftP P p ⟨a, f⟩ ↔ ∀ i j, p (f i j) := by
  erw [liftP_iff]
  constructor
  · rintro ⟨_, _, ⟨⟩, h⟩; exact h
  · intro h; exact ⟨a, f, rfl, h⟩

theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P α) :
    LiftR P r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    exact ⟨a, fun i j => (f i j).val.1, fun i j => (f i j).val.2,
      by erw [← xeq, h, map_eq]; rfl,
      by erw [← yeq, h, map_eq]; rfl,
      fun i j => (f i j).property⟩
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
    by erw [xeq, map_eq]; rfl,
    by erw [yeq, map_eq]; rfl⟩

theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) :
    supp P ⟨a, f⟩ i = fun x => ∃ j, f i j = x := by
  funext x
  apply propext
  simp only [supp]
  constructor
  · intro h
    apply h (p := fun i x => ∃ j, f i j = x)
    rw [liftP_iff']
    intro i j; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    intro p hp
    rw [liftP_iff'] at hp
    exact hp i j

end QPFTypes.MvPFunctor
