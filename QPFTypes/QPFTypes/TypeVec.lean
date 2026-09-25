/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import QPFTypes.TypeVec.Basic
public import QPFTypes.TypeVec.Arrow
public import QPFTypes.TypeVec.Prod
public import QPFTypes.TypeVec.Rel

/-!

# Tuples of types, and their categorical structure.

## Features

* `TypeVec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `appendFun f g` - appends a function g to an n-tuple of functions
* `dropFun f`     - drops the last function from an n+1-tuple
* `lastFun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.

This file is a modified version of `Mathlib.Data.TypeVec`, with `Fin2` replaced by `Fin`
throughout.

## Notes on Fin vs Fin2 API differences

The following `Fin` API is used where `Fin2` constructors/functions were used:
- `Fin.cases` replaces case analysis on `Fin2.fz`/`Fin2.fs` (for definitions and non-inductive proofs)
- `Fin.elim0` replaces `Fin2.elim0`
- `Fin.succ` replaces `Fin2.fs`
- `(0 : Fin (n+1))` replaces `Fin2.fz`

### Structural induction in proofs

`Fin2` supported structural induction directly:
```
induction i with
| fz => ...          -- base case: i = 0 : Fin2 (n+1), for any n
| fs n j ih => ...   -- step case: i = j.fs, IH for j : Fin2 n
```
whose key feature is that the motive `C : ∀ n, Fin2 n → Prop` quantifies over both `n` and the
index, so the IH is stated for a strictly smaller ambient dimension.

The direct `Fin` analog is `Fin.succRecOn` (argument-first) or `Fin.succRec` (argument-last), both
in core Lean 4 (`Init.Data.Fin.Lemmas`). Their motive also quantifies over both `n` and `i : Fin n`,
giving the same structural IH:
```
induction i using Fin.succRecOn with
| zero n => ...          -- base case: i = 0 : Fin (n+1), for any n
| succ n j ih => ...     -- step case: i = j.succ, IH for j : Fin n
```
Note that `n` in each branch is the *predecessor* dimension (so the `zero` branch has `i : Fin (n+1)`).
Variables depending on `n` (such as `TypeVec n`) are generalized automatically by the motive.

For *definitions*, direct pattern matching on `Fin` via `Fin.cases` (or `| ⟨0,_⟩ =>` / `| ⟨k+1,h⟩ =>`)
is cleaner than `Fin.succRec`, which is better suited to proofs.

### Direct analogs
- `Fin2.cases'` ↔ `Fin.cases` ✓
- `Fin2.elim0` ↔ `Fin.elim0` ✓
- Structural induction on `Fin2` ↔ `induction i using Fin.succRecOn` ✓
- No analog of `Fin2.toNat` needed — `Fin` already stores `.val : Nat`
-/
