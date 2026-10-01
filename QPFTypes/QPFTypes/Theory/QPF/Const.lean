/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import QPFTypes.Theory.PFunctor.Multivariate.Const
public import QPFTypes.Theory.QPF.Basic
public import QPFTypes.Theory.QPF.IsPolynomial

/-!
# Constant functors are QPFs

Constant functors map every type vector to the same target type. This is a useful
device for constructing data types from more basic types that are not actually
functorial. For instance, `Const n Nat` makes `Nat` into an `n`-ary functor that
can be used in a functor-based data type specification.
-/

@[expose] public section

universe u

namespace QPFTypes.QPF

open MvFunctor

/-- The constant `n`-ary functor, which maps every type vector to `A`. -/
def Const (n : Nat) (A : Type u) (_v : TypeVec.{u} n) : Type u :=
  A

namespace Const

variable {n : Nat} {A : Type u} {α β : TypeVec.{u} n}

instance inhabited [Inhabited A] : Inhabited (Const n A α) :=
  ⟨(default : A)⟩

/-- Constructor for the constant functor -/
protected def mk (x : A) : Const n A α := x

/-- Destructor for the constant functor -/
protected def get (x : Const n A α) : A := x

@[simp, grind =] protected theorem mk_get (x : Const n A α) : Const.mk (Const.get x) = x := rfl

@[simp, grind =] protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x := rfl

/-- `map` for the constant functor; the mapped function is simply discarded -/
protected def map (_f : α ⟹ β) : Const n A α → Const n A β := fun x => x

instance mvfunctor : MvFunctor (Const n A) where map := Const.map

theorem map_mk (f : α ⟹ β) (x : A) : f <$$> (Const.mk x : Const n A α) = Const.mk x := rfl

theorem get_map (f : α ⟹ β) (x : Const n A α) : Const.get (f <$$> x) = Const.get x := rfl

instance qpf : QPF (Const n A) where
  P := MvPFunctor.const n A
  abs x := MvPFunctor.const.get x
  repr x := MvPFunctor.const.mk n x
  abs_repr := by intros; rfl
  abs_map := by intros; rfl

/-- Constant functors are polynomial. -/
instance instIsPolynomial : IsPolynomial (Const n A) where
  repr_abs p := MvPFunctor.const.mk_get p

end Const

end QPFTypes.QPF
