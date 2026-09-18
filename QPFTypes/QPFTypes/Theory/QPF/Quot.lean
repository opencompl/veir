/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import QPFTypes.Theory.QPF.Basic

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `QPF`
-/

@[expose] public section
namespace QPFTypes.QPF

universe u

open MvFunctor

variable {n : Nat}
variable {F : TypeVec.{u} n → Type u}

section repr

variable [q : QPF F]
variable {G : TypeVec.{u} n → Type u} [MvFunctor G]
variable {FG_abs : ∀ {α}, F α → G α}
variable {FG_repr : ∀ {α}, G α → F α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `QPF` instances by transporting them across
surjective functions -/
@[instance_reducible]
def quotientQPF (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
    QPF G where
  P := q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by rw [abs_repr, FG_abs_repr]
  abs_map f p := by rw [abs_map, FG_abs_map]

end repr

section Rel

variable (R : ∀ ⦃α⦄, F α → F α → Prop)

/-- Functorial quotient type -/
def Quot1 (α : TypeVec n) :=
  Quot (@R α)

instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩

section

variable [MvFunctor F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `map` of the `Quot1` functor -/
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α → Quot1.{u} R β :=
  Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound <| Hfunc a b _ h

/-- `mvFunctor` instance for `Quot1` with well-behaved `R` -/
@[instance_reducible]
def Quot1.mvFunctor : MvFunctor (Quot1 R) where map := @Quot1.map _ _ R _ Hfunc

end

section

variable [q : QPF F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/--
Choose an element of the equivalence class using the axiom of choice.
Sound but noncomputable.
-/
-- Taken from Mathlib (`Mathlib/Data/Quot.lean`).
protected noncomputable def Quot.out {r : α → α → Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)

/-- `Quot1` is a QPF -/
@[instance_reducible]
noncomputable def relQuot : @QPF _ (Quot1 R) :=
  @quotientQPF n F q _ (QPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Classical.choose_spec (Quot.exists_rep _)) fun _f _x => rfl

end

end Rel

end QPF
