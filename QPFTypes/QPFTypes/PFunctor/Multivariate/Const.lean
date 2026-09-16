/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.PFunctor.Multivariate.Basic

/-!
# The constant polynomial functor.

The constant multivariate polynomial functor takes a `(A : Type u)`,
and produces a polynomial functor where this is the head,
and all children are empty.

This means `const n A` is equivalent to the source type A.
This equivalence is inhabited by `const.mk n` and `const.get`.
-/
@[expose] public section

namespace QPFTypes.MvPFunctor
open TypeVec

universe u

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Constant functor where the input object does not affect the output -/
def const (n : Nat) (A : Type u) : MvPFunctor n :=
  { A, B := fun _ _ => PEmpty }

namespace const

variable (n) {A : Type u} {α β : TypeVec.{u} n}

/-- Constructor for the constant functor -/
def mk (x : A) {α} : const n A α :=
  ⟨x, fun _ a => PEmpty.elim a⟩

variable {n}

/-- Destructor for the constant functor -/
def get (x : const n A α) : A :=
  x.1

@[simp]
theorem get_map (f : α ⟹ β) (x : const n A α) :
    const.get ((const n A).map f x) = const.get x := by
  cases x; rfl

@[simp]
theorem get_mk (x : A) : const.get (const.mk n x : const n A α) = x := rfl

@[simp]
theorem mk_get (x : const n A α) : const.mk n (const.get x) = x := by
  cases x
  simp only [const.get, const.mk]
  congr 1
  funext _ a
  exact PEmpty.elim a

end const

end QPFTypes.MvPFunctor
