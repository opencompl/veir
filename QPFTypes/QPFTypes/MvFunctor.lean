/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import QPFTypes.TypeVec

/-!

# Functors between the category of tuples of types, and the category Type

Features:

* `MvFunctor n` : the type class of multivariate functors
* `f <$$> x`    : notation for map

-/

@[expose] public section

namespace QPFTypes

universe u v w

/-- Multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
class MvFunctor {n : Nat} (F : TypeVec n → Type _) where
  /-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β`. -/
  map : ∀ {α β : TypeVec n}, α ⟹ β → F α → F β

/-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β` -/
scoped infixr:100 " <$$> " => MvFunctor.map

variable {n : Nat}

open MvFunctor

namespace MvFunctor

variable {α β : TypeVec.{u} n} {F : TypeVec.{u} n → Type v} [MvFunctor F]

/-- predicate lifting over multivariate functors -/
def LiftP {α : TypeVec n} (P : ∀ i, α i → Prop) (x : F α) : Prop :=
  ∃ u : F (fun i => Subtype (P i)), (fun i => @Subtype.val _ (P i)) <$$> u = x

/-- relational lifting over multivariate functors -/
def LiftR {α : TypeVec n} (R : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) : Prop :=
  ∃ u : F (fun i => { p : α i × α i // R p.fst p.snd }),
    (fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.fst) <$$> u = x ∧
      (fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.snd) <$$> u = y

end MvFunctor

open TypeVec in
/-- laws for `MvFunctor` -/
class LawfulMvFunctor {n : Nat} (F : TypeVec n → Type _) [MvFunctor F] : Prop where
  /-- `map` preserved identities, i.e., maps identity on `α` to identity on `F α` -/
  id_map : ∀ {α : TypeVec n} (x : F α), TypeVec.id <$$> x = x
  /-- `map` preserves compositions -/
  comp_map :
    ∀ {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) <$$> x = h <$$> g <$$> x

open Nat TypeVec

namespace MvFunctor

export LawfulMvFunctor (comp_map)

open LawfulMvFunctor

variable {α β γ : TypeVec.{u} n}
variable {F : TypeVec.{u} n → Type v} [MvFunctor F]
variable (P : α ⟹ «repeat» n Prop) (R : α ⊗ α ⟹ «repeat» n Prop)

/-- adapt `MvFunctor.LiftP` to accept predicates as arrows -/
def LiftP' : F α → Prop :=
  MvFunctor.LiftP fun i x => ofRepeat <| P i x

/-- adapt `MvFunctor.LiftR` to accept relations as arrows -/
def LiftR' : F α → F α → Prop :=
  MvFunctor.LiftR @fun i x y => ofRepeat <| R i <| TypeVec.prod.mk _ x y

variable [LawfulMvFunctor F]

@[simp, grind =]
theorem id_map (x : F α) : TypeVec.id <$$> x = x :=
  LawfulMvFunctor.id_map x

@[simp]
theorem id_map' (x : F α) : (fun _i a => a) <$$> x = x :=
  id_map x

@[grind =]
theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h <$$> g <$$> x = (h ⊚ g) <$$> x :=
  Eq.symm <| comp_map _ _ _

variable (F) in
theorem exists_iff_exists_of_mono {P : F α → Prop} {q : F β → Prop}
    (f : α ⟹ β) (g : β ⟹ α)
    (h₀ : f ⊚ g = TypeVec.id)
    (h₁ : ∀ u : F α, P u ↔ q (f <$$> u)) :
    (∃ u : F α, P u) ↔ ∃ u : F β, q u := by
  constructor <;> rintro ⟨u, h₂⟩
  · refine ⟨f <$$> u, ?_⟩
    apply (h₁ u).mp h₂
  · refine ⟨g <$$> u, ?_⟩
    rw [h₁]
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]

/-- Any type function that is (extensionally) equivalent to a functor, is itself a functor -/
abbrev ofEquiv {F F' : TypeVec.{u} n → Type _} [MvFunctor F']
    (toFun : ∀ {α}, F α → F' α) (invFun : ∀ {α}, F' α → F α) :
    MvFunctor F where
  map f x := invFun <| f <$$> toFun x

end MvFunctor

end QPFTypes
