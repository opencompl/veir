/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.Theory.PFunctor.Multivariate.Comp
public import QPFTypes.Theory.QPF.Basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/

@[expose] public section


universe u

namespace QPFTypes.QPF

open MvFunctor

variable {n m : Nat} (F : TypeVec.{u} n → Type _) (G : Fin n → TypeVec.{u} m → Type u)

/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin n ↦ G i v

namespace Comp

open MvPFunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

instance [I : Inhabited (F fun i : Fin n ↦ G i α)] : Inhabited (Comp F G α) := I

/-- Constructor for functor composition -/
protected def mk (x : F fun i ↦ G i α) : Comp F G α := x

/-- Destructor for functor composition -/
protected def get (x : Comp F G α) : F fun i ↦ G i α := x

@[simp]
protected theorem mk_get (x : Comp F G α) : Comp.mk (Comp.get x) = x := rfl

@[simp]
protected theorem get_mk (x : F fun i ↦ G i α) : Comp.get (Comp.mk x) = x := rfl

section
variable [MvFunctor F] [∀ i, MvFunctor <| G i]

/-- map operation defined on a vector of functors -/
protected def map' : (fun i : Fin n ↦ G i α) ⟹ fun i : Fin n ↦ G i β := fun _i ↦ map f

/-- The composition of functors is itself functorial -/
protected def map : (Comp F G) α → (Comp F G) β :=
  (map fun _i ↦ map f : (F fun i ↦ G i α) → F fun i ↦ G i β)

instance : MvFunctor (Comp F G) where map f := Comp.map f

theorem map_mk (x : F fun i ↦ G i α) :
    f <$$> Comp.mk x = Comp.mk ((fun i (x : G i α) ↦ f <$$> x) <$$> x) := rfl

theorem get_map (x : Comp F G α) :
    Comp.get (f <$$> x) = (fun i (x : G i α) ↦ f <$$> x) <$$> Comp.get x := rfl

end

set_option backward.isDefEq.respectTransparency false in
instance inst [QPF F] [∀ i, QPF <| G i] : QPF (Comp F G) where
  P := MvPFunctor.comp (P F) fun i ↦ P <| G i
  abs := Comp.mk ∘ (map fun _ ↦ abs) ∘ abs ∘ MvPFunctor.comp.get
  repr {α} := MvPFunctor.comp.mk ∘ repr ∘
              (map fun i ↦ (repr : G i α → (fun i : Fin n ↦ Obj (P (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp +unfoldPartialApp only [Function.comp_def, comp.get_mk, abs_repr,
      map_map, TypeVec.comp, MvFunctor.id_map', Comp.mk_get]
  abs_map := by
    intros
    simp only [(· ∘ ·)]
    rw [← abs_map]
    simp +unfoldPartialApp only [comp.get_map, map_map, TypeVec.comp,
      abs_map, map_mk]

end Comp

end QPFTypes.QPF
