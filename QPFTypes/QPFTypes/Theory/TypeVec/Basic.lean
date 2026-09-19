/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

/-!

# Tuples of types

## Features

* `TypeVec n` - n-tuples of types

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.

This file is a modified version of `Mathlib.Data.TypeVec`, with `Fin2` replaced by `Fin` throughout,
this is also only a subset of the implemented features,
the rest are distributed in this directory.
-/
@[expose] public section

universe u v w x

namespace QPFTypes

/-- n-tuples of types, as a category -/
def TypeVec (n : Nat) :=
  Fin n → Type _

instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

variable {n : Nat}

/-- Support for extending a `TypeVec` by one element.
  At index `0` (i.e. `Fin2.fz`) returns `β`; at index `i.succ` (i.e. `Fin2.fs i`) returns `α i`. -/
def TypeVec.append1 (α : TypeVec n) (β : Type _) : TypeVec (n + 1) :=
  Fin.cases β α

@[inherit_doc] scoped infixl:67 " ::: " => TypeVec.append1

/--
Extend a `TypeVec` with a new element at the _front_ of the list.
-/
-- TODO(WS): When do we use this?
def TypeVec.cons (α : Type u) (αs : TypeVec.{u} n) : TypeVec (n + 1) :=
  Fin.lastCases α αs
@[inherit_doc] scoped infixr:67 " <: " => TypeVec.cons

namespace TypeVec

def nil : TypeVec 0 :=
  Fin.elim0

/-- retain only a `n-length` prefix of the argument -/
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.succ

/-- take the last value of a `(n+1)-length` vector -/
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α 0

/-- take the first value of a `(n+1)-length` vector -/
def head (α : TypeVec.{u} (n + 1)) : Type _ :=
  α (.last _)

/-- retain only a `n-length` _suffix_ of the argument -/
def tail (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.castSucc

section HeadTail
variable (βs : TypeVec.{u} n) (β : Type u)

@[grind =] theorem head_append1 :
    (βs ::: β).head = match n with
      | 0 => β
      | _+1 => βs.head := by
  cases n <;> grind [append1, head, Fin.last]

@[grind =] theorem tail_append1 :
    (βs ::: β).tail = match n with
      | 0 => nil
      | _+1 => βs.tail ::: β := by
  funext i
  cases n
  · exact i.elim0
  · cases i using Fin.cases
    <;> rfl

@[simp, grind =] theorem head_cons : (β <: βs).head = β := by
  grind [head, cons]
@[simp, grind =] theorem tail_cons : (β <: βs).tail = βs := by
  funext i; grind [tail, cons]

@[simp, grind =] theorem cons_head_tail {βs : TypeVec (n+1)} :
    βs.head <: βs.tail = βs := by
  funext i; cases i using Fin.lastCases
  <;> grind [cons, head, tail]

end HeadTail

instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α 0)] : Inhabited (last α) :=
  ⟨show α 0 from default⟩

theorem drop_append1 {α : TypeVec n} {β : Type _} {i : Fin n} : drop (append1 α β) i = α i :=
  rfl

@[simp]
theorem drop_append1' {α : TypeVec n} {β : Type _} : drop (append1 α β) = α :=
  funext fun _ => drop_append1

theorem last_append1 {α : TypeVec n} {β : Type _} : last (append1 α β) = β :=
  rfl

@[simp]
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α := by
  funext i
  cases i using Fin.cases
  <;> rfl

/-- cases on `(n+1)-length` vectors -/
@[elab_as_elim]
def append1Cases {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ]; apply H

@[simp]
theorem append1_cases_append1 {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl

-- TODO(WS): Delete name
instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun _ _ => funext fun i => i.elim0⟩

-- TODO(WS): Redundant
theorem eq_nil (βs : TypeVec 0) : βs = nil := by
  funext i; exact i.elim0

/-- cases distinction for 0-length type vector -/
-- TODO(WS): Mark @[elab_as_elim]
protected def casesNil {β : TypeVec 0 → Sort _} (f : β Fin.elim0) : ∀ v, β v :=
  fun v => cast (by congr; funext i; exact i.elim0) f

/-- cases distinction for (n+1)-length type vector -/
-- TODO(WS): Mark @[elab_as_elim]
protected def casesCons (n : Nat) {β : TypeVec (n + 1) → Sort _}
    (f : ∀ t (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)

protected theorem casesNil_append1 {β : TypeVec 0 → Sort _} (f : β Fin.elim0) :
    TypeVec.casesNil f Fin.elim0 = f :=
  rfl

protected theorem casesCons_append1 (n : Nat) {β : TypeVec (n + 1) → Sort _}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl


/-- `repeat n t` is a `n-length` type vector that contains `n` occurrences of `t` -/
-- TODO(WS):
-- 1. This could just be the constant function, which has better defeqs,
-- 2. fundementally this is also just a constant function so should mby not be called repeat
def «repeat» : ∀ (n : Nat), Type u → TypeVec n
  | 0, _ => Fin.elim0
  | Nat.succ i, t => append1 («repeat» i t) t
