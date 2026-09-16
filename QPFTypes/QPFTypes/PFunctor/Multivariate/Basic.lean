/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.TypeVec
public import QPFTypes.MvFunctor
public import QPFTypes.PFunctor.Univariate.Basic

/-!
# Multivariate polynomial functors

Multivariate polynomial functors map a type vector `α` to the type `Σ a : A, B a ⟹ α`,
with `A : Type` and `B : A → TypeVec n`. They interact well with Lean's inductive
definitions because they guarantee that occurrences of `α` are positive.
-/
@[expose] public section

namespace QPFTypes
open TypeVec

universe u

/-- Multivariate polynomial functors -/
structure MvPFunctor (n : Nat) where
  /-- The head type -/
  A : Type u
  /-- The child family of type vectors -/
  B : A → TypeVec.{u} n

namespace MvPFunctor

variable {n m : Nat} (P : MvPFunctor.{u} n)

/-- Applying `P` to an object of `TypeVec` -/
@[coe]
def Obj (α : TypeVec.{u} n) : Type u :=
  Σ a : P.A, P.B a ⟹ α
instance : CoeFun (MvPFunctor.{u} n) (fun _ => TypeVec.{u} n → Type u) where
  coe := Obj

/-! ### Inhabitedness -/

instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, default⟩⟩

instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [∀ i, Inhabited (α i)] :
    Inhabited (P α) :=
  ⟨⟨default, fun _ _ => default⟩⟩

/-! ### Mapping Functions -/

/-- Applying `P` to a morphism of `TypeVec` -/
instance : MvFunctor P where
  map f := fun ⟨a, g⟩ => ⟨a, f ⊚ g⟩
@[grind] abbrev map (f : α ⟹ β) (x : P α) := f <$$> x

section MapLemmas

@[simp, grind =]
theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
    P.map g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
  rfl

@[simp, grind =]
theorem id_map {α : TypeVec n} : ∀ x : P α, P.map TypeVec.id x = x
  | ⟨_, _⟩ => rfl

@[simp, grind =]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
    ∀ x : P α, P.map (g ⊚ f) x = P.map g (P.map f x)
  | ⟨_, _⟩ => rfl

instance : LawfulMvFunctor P where
  id_map := by simp
  comp_map := by simp

end MapLemmas

/-
Decomposing an (n+1)-ary polynomial functor.
-/

variable (P : MvPFunctor.{u} (n + 1))

/-- Split polynomial functor, get an n-ary functor from an `(n+1)`-ary functor -/
def drop : MvPFunctor n where
  A := P.A
  B a := (P.B a).drop

/-- Split polynomial functor, get a univariate functor from an `(n+1)`-ary functor -/
def last : PFunctor where
  A := P.A
  B a := (P.B a).last

/-- Append arrows of a polynomial functor application -/
abbrev appendContents {α : TypeVec n} {β : Type _} {a : P.A}
    (f' : P.drop.B a ⟹ α) (f : P.last.B a → β) : P.B a ⟹ (α ::: β) :=
  splitFun f' f

end MvPFunctor
