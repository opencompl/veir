/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import QPFTypes.TypeVec.Basic
public import QPFTypes.TypeVec.Arrow

/-!

# The product object in the category typevectors

## Features

* `α ⊗ β` - products of n-tuples
* `α ⊗' β` - products of n-tuples of maps

Also, support functions for operating with n-tuples of types, such as:

* `fst : α ⊗ β ⇒ α` - first projection
* `snd : α ⊗ β ⇒ α` - second projection
* `mk f g : α ⊗ β`  - unique constructor

This file is a modified version of `Mathlib.Data.TypeVec`, with `Fin2` replaced by `Fin` throughout,
this is also only a subset of the implemented features,
the rest are distributed in this directory.
-/

@[expose] public section

universe u v w x

namespace QPFTypes

variable {n : Nat}

namespace TypeVec

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
def prod : ∀ {n}, TypeVec.{u} n → TypeVec.{u} n → TypeVec n
  | 0, _, _ => Fin.elim0
  | n + 1, α, β => (@prod n (drop α) (drop β)) ::: (last α × last β)

-- TODO: this ought to be scoped to the parent QPFTypes namespace
@[inherit_doc] scoped infixl:45 " ⊗ " => TypeVec.prod

/-- left projection of a `prod` vector -/
def prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | 0, _, _, i => i.elim0
  | .succ _, α, β, i =>
    Fin.cases (motive := fun i => (α ⊗ β) i → α i)
      Prod.fst
      (fun j => @prod.fst _ (drop α) (drop β) j)
      i

/-- right projection of a `prod` vector -/
def prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | 0, _, _, i => i.elim0
  | .succ _, α, β, i =>
    Fin.cases (motive := fun i => (α ⊗ β) i → β i)
      Prod.snd
      (fun j => @prod.snd _ (drop α) (drop β) j)
      i

/-- introduce a product where both components are the same -/
def prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | 0, _, i => i.elim0
  | .succ _, α, i =>
    Fin.cases (motive := fun i => α i → (α ⊗ α) i)
      (fun x => (x, x))
      (fun j => @prod.diag _ (drop α) j)
      i

/-- constructor for `prod` -/
def prod.mk : ∀ {n} {α β : TypeVec.{u} n} (i : Fin n), α i → β i → (α ⊗ β) i
  | 0, _, _, i => i.elim0
  | .succ _, α, β, i =>
    Fin.cases (motive := fun i => α i → β i → (α ⊗ β) i)
      Prod.mk
      (fun j => @prod.mk _ (drop α) (drop β) j)
      i

@[simp]
theorem prod_fst_mk {α β : TypeVec n} (i : Fin n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by
  induction i using Fin.succRecOn with
  | zero n => rfl
  | succ n j ih => exact @ih (drop α) (drop β) a b

@[simp]
theorem prod_snd_mk {α β : TypeVec n} (i : Fin n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by
  induction i using Fin.succRecOn with
  | zero n => rfl
  | succ n j ih => exact @ih (drop α) (drop β) a b

/-- `prod` is functorial -/
protected def prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | 0, _, _, _, _, _, _, i => i.elim0
  | .succ _, α, α', β, β', x, y, i =>
    Fin.cases (motive := fun i => (α ⊗ α') i → (β ⊗ β') i)
      (fun a => (x 0 a.1, y 0 a.2))
      (fun j => @prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) j)
      i

-- TODO: this ought to be scoped to the parent QPFTypes namespace
@[inherit_doc] scoped infixl:45 " ⊗' " => TypeVec.prod.map

theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.prod.fst := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; cases a; rfl
  | succ n j ih => exact ih (dropFun f) (dropFun g)

theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.prod.snd := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; cases a; rfl
  | succ n j ih => exact ih (dropFun f) (dropFun g)

theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; rfl
  | succ n j ih => exact @ih (drop α)

theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; rfl
  | succ n j ih => exact @ih (drop α)

theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) := by
  intro n α β
  funext i
  induction i using Fin.succRecOn with
  | zero n => funext a; cases a; rfl
  | succ n j ih => exact @ih (drop α) (drop β)

theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {p p' q q' : Type u}
    {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : p → p'} {g₁ : q → q'} :
    ((f₀ ⊗' g₀) ::: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · funext a; cases a; rfl
  · rfl

@[simp]
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag := by
  rfl

@[simp]
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') := by
  rfl

@[simp]
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = Prod.map (lastFun f) (lastFun f') := by
  rfl

@[simp]
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id := prod_id

section curry

/-- given `F : TypeVec.{u} (n+1) → Type u`, `curry F : Type u → TypeVec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
def Curry (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)

instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type _) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I

end curry
