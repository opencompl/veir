module

public import Veir.Interpreter.RuntimeValue.Conforms
public meta import Lean

import all Veir.Interpreter.RuntimeValue.Conforms

open Lean Meta Simp

/-!
This file defines the necessary simp and simproc lemmas to transform `ArrayConforms` predicates
into nested existentials of `Conforms` predicates, and then to transform those into the
corresponding `RuntimeValue` predicates for known types. For example:
`ArrayConforms operands #[.of IntegerType intType, t₂]` becomes
`∃ x₁, Conforms x₁ (.of IntegerType intType) ∧ ∃ x₂, Conforms x₂ t₂ ∧ operands = #[x₁, x₂]` with
`simp`.
-/

public section

namespace Veir.RuntimeValue

/-!
## ArrayConforms Expansion

This section defines `expandArrayShape`, a simproc that expands `ArrayConforms` for a literal array
of types into a nested existential with one `Conforms` condition per entry. For example,
`ArrayConforms operands #[t₁, t₂]` becomes
`∃ x₁, Conforms x₁ t₁ ∧ ∃ x₂, Conforms x₂ t₂ ∧ operands = #[x₁, x₂]`.
-/

namespace ListConforms.Shape

/-!
These helpers are used to implement `expandArrayShape`. They need to be public so that the simproc
can use them in generated proofs in importing modules, though they are implementation details.
-/

theorem expand_nil (P : List RuntimeValue → Prop) :
    (∃ vs, ListConforms vs [] ∧ P vs) ↔ P [] := by
  constructor
  · grind
  · intro
    exists []

theorem expand_cons (t : TypeAttr) {ts : List TypeAttr}
    {tail : (List RuntimeValue → Prop) → Prop}
    (htail : ∀ P, (∃ vs, ListConforms vs ts ∧ P vs) ↔ tail P)
    (P : List RuntimeValue → Prop) :
    (∃ vs, ListConforms vs (t :: ts) ∧ P vs) ↔
      ∃ v, Conforms v t ∧ tail (fun rest => P (v :: rest)) := by
  constructor
  · grind
  · rintro ⟨v, hv, hr⟩
    obtain ⟨rest, hr, hp⟩ := (htail _).mpr hr
    exists v :: rest

end ListConforms.Shape

theorem ArrayConforms.Shape.expand_array {ts : List TypeAttr}
    {expanded : (List RuntimeValue → Prop) → Prop}
    (h : ∀ P, (∃ vs, ListConforms vs ts ∧ P vs) ↔ expanded P)
    (operands : Array RuntimeValue) :
    ArrayConforms operands ts.toArray ↔ expanded (fun vs => operands = vs.toArray) := by
  rw [← h]
  simp only [ArrayConforms.iff_listConforms_toList,
    List.eq_toArray_iff, exists_eq_right']

/--
From a list of type attributes `[t₁, t₂, ...]`, build the theorem
```
∀ P, (∃ vs, ListConforms [t₁, t₂, ...] vs ∧ P vs) ↔
(∃ x₁, Conforms x₁ t₁ ∧ ∃ x₂, Conforms x₂ t₂ ∧ ... ∧ P [x₁, x₂, ...])
```
-/
private meta def buildArrayExpansion : List Expr → MetaM Expr
  | [] => return mkConst ``ListConforms.Shape.expand_nil
  | t :: ts => do
    let ht ← buildArrayExpansion ts
    -- Instantiate the type parameter explicitly: it may be completely unknown.
    let step ← withTransparency .default <| mkAppM ``ListConforms.Shape.expand_cons #[t, ht]
    return step

/--
Simplify `ArrayConforms xs #[t₁, t₂, ...]` into a nested existential with one `Conforms` condition
per entry, and a final equality of the array to the constructed list. For example,
`ArrayConforms xs #[t₁, t₂]` becomes `∃ x₁, Conforms x₁ t₁ ∧ ∃ x₂, Conforms x₂ t₂ ∧ xs = #[x₁, x₂]`.
-/
simproc_decl expandArrayShape (ArrayConforms _ _) := fun e => do
  let_expr ArrayConforms operands types := e | return .continue
  let some tys ← getArrayLit? types | return .continue
  /- Build the equality on `ListConforms`. -/
  let hlist ← buildArrayExpansion tys.toList
  /- Convert the equality to `ArrayConforms`. -/
  let h ← mkAppM ``ArrayConforms.Shape.expand_array #[hlist, operands]
  let ht ← inferType h
  let_expr Iff _ rhs := ht
    | panic! "Internal error in expandArrayShape: unexpected type for expand_array: {ht}"
  return .visit { expr := rhs, proof? := some (← mkAppM ``propext #[h]) }

attribute [simp] expandArrayShape

/-!
## Existential RuntimeValue simplification

The following lemmas, in addition with the `simp` lemmas that target `Conforms` with specific
constructors, simplify `∃ x, Conforms x t ∧ body x` into `body (constr val)` for the appropriate
`RuntimeValue` constructor `constr`.
-/

@[simp]
theorem exists_eq_apply_and {T : Type} {U : T → RuntimeValue} {P : RuntimeValue → Prop} :
    (∃ v, (∃ val, v = U val) ∧ P v) ↔ ∃ val, P (U val) := by grind

@[simp]
theorem exists_eq_apply_and_condition {T : Type} {U : T → RuntimeValue}
    {Q : T → Prop} {P : RuntimeValue → Prop} :
    (∃ v, (∃ val, v = U val ∧ Q val) ∧ P v) ↔ ∃ val, Q val ∧ P (U val) := by grind

end Veir.RuntimeValue
