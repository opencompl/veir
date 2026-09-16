/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import QPFTypes.TypeVec.Basic
public import QPFTypes.TypeVec.Arrow

/-!

# Relational lifting over typevectors

## Features

* `PredLast α p` - Lift a predicate to the final value of typevecs
* `RelLast α r`  - Relates last value of typevecs, equates the rest

This file is a modified version of `Mathlib.Data.TypeVec`, with `Fin2` replaced by `Fin` throughout,
this is also only a subset of the implemented features,
the rest are distributed in this directory.
-/

@[expose] public section

universe u v w x

namespace QPFTypes

variable {n : Nat}

namespace TypeVec

-- for lifting predicates and relations
/-- `PredLast α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def PredLast (α : TypeVec n) {β : Type _} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop :=
  fun i => Fin.cases (motive := fun i => (α.append1 β) i → Prop) p (fun _ _ => True) i

/-- `RelLast α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r`
and all the other elements are equal. -/
def RelLast (α : TypeVec n) {β γ : Type u} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop :=
  fun i => Fin.cases (motive := fun i => (α.append1 β) i → (α.append1 γ) i → Prop)
    r (fun _ a b => a = b) i
