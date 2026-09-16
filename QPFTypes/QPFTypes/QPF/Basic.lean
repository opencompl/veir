/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.MvFunctor
public import QPFTypes.PFunctor.Multivariate.Basic

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive ListShape (a b : Type)
  | nil : ListShape
  | cons : a -> b -> ListShape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def List (a : Type) := fix ListShape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def Multiset (a : Type) := QPF.quot List.perm List a -- not the actual notion
```

And `Multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive Tree (a : Type)
  | node : a -> Multiset Tree -> Tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive Tree' (a : Type)
| node : a -> Multiset Tree' -> Tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`Tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

* constructions
  * Fix
  * Cofix
  * Quot
  * Comp
  * Sigma / Pi
  * Prj
  * Const

each proves that some operations on functors preserves the QPF structure
-/

@[expose] public section

/-!
## Reference

[Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

namespace QPFTypes
open TypeVec

universe u

/-- Multivariate quotients of polynomial functors. -/
class QPF {n : Nat} (F : TypeVec.{u} n → Type _) extends MvFunctor F where
  P : MvPFunctor.{u} n
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α ⟹ β) (p : P α), abs (P.map f p) = f <$$> abs p

namespace QPF

attribute [grind =] abs_map abs_repr

variable {n : Nat} {F : TypeVec.{u} n → Type _} [q : QPF F]

open MvFunctor (LiftP LiftR)

/-!
### Show that every QPF is a lawful MvFunctor.
-/

protected theorem id_map {α : TypeVec n} (x : F α) : TypeVec.id <$$> x = x := by
  rw [← abs_repr x, ← abs_map]
  rfl

@[simp, grind =, grind =_]
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
    (g ⊚ f) <$$> x = g <$$> f <$$> x := by
  rw [← abs_repr x, ← abs_map, ← abs_map, ← abs_map]
  rfl

instance (priority := 100) lawfulMvFunctor : LawfulMvFunctor F where
  id_map := @QPF.id_map n F _
  comp_map := @comp_map n F _

-- Lifting predicates and relations
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : F α) :
    LiftP p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, ?_⟩
    · erw [← hy, ← abs_repr y, h, ← abs_map]; rfl
    · intro i j; apply (f i j).property
  · rintro ⟨a, f, h₀, h₁⟩
    refine ⟨abs ⟨a, fun i j => ⟨f i j, h₁ i j⟩⟩, ?_⟩
    erw [← abs_map, h₀]; rfl

theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) :
    LiftR r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd, ?_, ?_, ?_⟩
    · erw [← xeq, ← abs_repr u, h, ← abs_map]; rfl
    · erw [← yeq, ← abs_repr u, h, ← abs_map]; rfl
    · intro i j; exact (f i j).property
  · rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
    refine ⟨abs ⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩, ?_, ?_⟩
    · erw [xeq, ← abs_map]; rfl
    · erw [yeq, ← abs_map]; rfl

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def IsUniform : Prop :=
  ∀ ⦃α : TypeVec n⦄ (a a' : q.P.A) (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i j, ∃ j', f i j = f' i j'

/-- does `abs` preserve `liftp`? -/
def LiftPPreservation : Prop :=
  ∀ ⦃α : TypeVec n⦄ (p : ∀ ⦃i⦄, α i → Prop) (x : q.P α), LiftP p (abs x) ↔ LiftP p x

/-! ### ofEquiv -/

/-- Any type function `F` that is (extensionally) equivalent to a QPF, is itself a QPF,
assuming that the functorial map of `F` behaves similar to `MvFunctor.ofEquiv eqv` -/
abbrev ofEquiv {F F' : TypeVec.{u} n → Type _} [q : QPF F'] [MvFunctor F]
    (toF : ∀ {α}, F α → F' α)
    (invF : ∀ {α}, F' α → F α)
    (left_inv : ∀ {α} (x : F α), invF (toF x) = x)
    (right_inv : ∀ {α} (x : F' α), toF (invF x) = x)
    (map_eq : ∀ {α β} (f : α ⟹ β) (a : F α), f <$$> a = invF (f <$$> toF a) := by intros; rfl) :
    QPF F where
  P        := q.P
  abs x    := invF (q.abs x)
  repr x   := q.repr (toF x)
  abs_repr := by simp [q.abs_repr, left_inv]
  abs_map  := by simp [q.abs_map, map_eq, right_inv]

end QPF

/-- Every polynomial functor is a (trivial) QPF -/
instance MvPFunctor.instQPFObj {n} (P : MvPFunctor n) : QPF P where
  map := P.map
  P := P
  abs := id
  repr := id
  abs_repr := by intros; rfl
  abs_map := by intros; rfl

end QPFTypes
