/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.PFunctor.Multivariate.Basic

/-!
# Composition of polynomial functors

Given an `n`-ary polynomial functor `P`, and a `n`-vector of `m`-ary polynomial functors `Qᵢ`,
their composition `P.comp Q` is the unique polynomial functor which,
when applied to a vector of `m` types, is equivalent to the pointwise composition:
`(P.comp Q) α ≃ P (Q₁ α) (Q₂ α) ⋯ (Qₙ α)`.
-/
@[expose] public section

namespace QPFTypes.MvPFunctor
open TypeVec

universe u

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Functor composition on polynomial functors -/
def comp (P : MvPFunctor.{u} n) (Q : Fin n → MvPFunctor.{u} m) : MvPFunctor m where
  A := Σ a : P.A, ∀ i, P.B a i → (Q i).A
  B a i := Σ (j : Fin n) (b : P.B a.1 j), (Q j).B (a.2 j b) i

namespace comp

variable {P} {Q : Fin n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

/-- Constructor for functor composition -/
def mk (x : P (fun i => Q i α)) : comp P Q α :=
  ⟨⟨x.1, fun i a => (x.2 i a).1⟩, fun i a => (x.2 a.1 a.2.1).2 i a.2.2⟩

/-- Destructor for functor composition -/
def get (x : comp P Q α) : P (fun i => Q i α) :=
  ⟨x.1.1, fun i a => ⟨x.1.2 i a, fun j b => x.2 j ⟨i, ⟨a, b⟩⟩⟩⟩

theorem get_map (f : α ⟹ β) (x : comp P Q α) :
    comp.get ((comp P Q).map f x) =
    P.map (fun i (y : Q i α) => (Q i).map f y) (comp.get x) :=
  rfl

@[simp]
theorem get_mk (x : P (fun i => Q i α)) : comp.get (comp.mk x) = x :=
  rfl

@[simp]
theorem mk_get (x : comp P Q α) : comp.mk (comp.get x) = x :=
  rfl

end MvPFunctor.comp

