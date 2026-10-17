module

import Std.Internal.Order.Basic

/-!
Coinductive predicates up-to companion based on tower induction
This implements some of the theories of https://doi.org/10.1007/978-3-319-57418-9_17
-/

public section

namespace Tower

open Lean.Order

variable {α} [L: CompleteLattice α] (f : α → α)

/-- Tower induction -/
inductive tower : α → Prop where
  | chain {x} (h : tower x) : tower (f x)
  | inf (P : α → Prop) : (forall x, P x → tower x) → tower (inf P)

/-- An element of a tower -/
structure Chain where
  elem : α
  hTower : tower f elem

attribute [coe] Chain.elem

/-- Tower-based definition of the companion -/
noncomputable def cpn (x : α) := inf (fun y : α => tower f y ∧ x ⊑ y)

theorem cpn_mon : monotone (cpn f) := by
  unfold monotone
  intros x y
  unfold cpn
  rw [inf_spec]
  intros h z h'
  apply inf_le
  constructor
  · grind
  · apply PartialOrder.rel_trans
    apply h
    grind

theorem le_x_cpn_x : forall (x : α), x ⊑ cpn f x := by
  grind [cpn, inf_spec]

theorem cpn_cpn : forall x, cpn f (cpn f x) = cpn f x := by
  intros x
  apply PartialOrder.rel_antisymm
  · apply inf_le
    constructor <;> try apply PartialOrder.rel_refl
    apply tower.inf
    grind
  · apply cpn_mon
    apply le_x_cpn_x

theorem tower_cpn : forall x, tower f x ↔ cpn f x = x := by
  intros x
  constructor
  · intros h
    unfold cpn
    apply PartialOrder.rel_antisymm
    · apply inf_le
      constructor <;> try apply PartialOrder.rel_refl
      apply h
    · apply le_inf
      grind
  · intros h
    rw [<-h]
    unfold cpn
    apply tower.inf
    grind

theorem cpn_f_cpn : forall x, f (cpn f x) = cpn f (f (cpn f x)) := by
  intros x
  apply PartialOrder.rel_antisymm
  · apply le_inf
    intros y h
    grind
  · apply inf_le
    constructor
    · apply tower.chain
      rw [tower_cpn]
      apply cpn_cpn
    · rfl

@[expose]
def inf_closed (P : α → Prop) := (forall M : α → Prop, (forall m, M m → P m) -> P (inf M))

theorem tower_ind_cpn : forall (P : α → Prop),
    inf_closed P →
    (forall x, P (cpn f x) → P (f (cpn f x))) →
    forall x, P (cpn f x) := by
  intros P h h' x
  unfold inf_closed at h
  apply h
  intros y h''
  have h''' := h''.1
  clear x h''
  induction h'''
  case chain z h1 ih =>
    rw [tower_cpn] at h1
    rw [<-h1]
    apply h'
    rw [h1]
    apply ih
  case inf Q h'' ih =>
    apply h
    exact ih

/-- The main induction principle for chains -/
theorem tower_ind : forall (P : α → Prop),
    inf_closed P →
    (forall x : Chain f, P x.elem → P (f x.elem)) →
    forall x : Chain f, P x.elem := by
  intros P h h' x
  unfold inf_closed at h
  rcases x with ⟨x, ht⟩
  simp only
  induction ht
  case chain y ht ih =>
    apply (h' ⟨y, ht⟩)
    apply ih
  case inf Q h'' ih =>
    apply h
    exact ih

noncomputable def bot := L.sup (fun _ => False)

/-- Companion-based definition of greatest fixpoint -/
noncomputable abbrev gfp := cpn f bot

/-- Standard definition of greatest fixpoint -/
noncomputable def gfp' := L.sup (fun x => x ⊑ f x)

theorem bot_le : forall x : α, Tower.bot ⊑ x := by
  intros x
  apply sup_le
  simp

theorem f_gfp' : monotone f → f (gfp' f) = gfp' f := by
  intros hmon
  apply PartialOrder.rel_antisymm
  · apply le_sup
    apply hmon
    apply sup_le
    intros y h
    apply L.rel_trans
    apply h
    apply hmon
    apply le_sup
    apply h
  · apply sup_le
    intros y h
    apply L.rel_trans
    apply h
    apply hmon
    apply le_sup
    apply h

/-- The standard and companion-based definitions of greatest fixpoint are equivalent -/
theorem cpn_gfp : monotone f → gfp f = gfp' f := by
  intros hmon
  apply PartialOrder.rel_antisymm
  · apply le_sup
    rw [cpn_f_cpn (f := f) (x := Tower.bot)]
    apply cpn_mon
    apply Tower.bot_le
  · apply tower_ind_cpn
    · unfold inf_closed
      intros M h'
      apply le_inf
      apply h'
    · intros y ch
      rw [<-f_gfp']
      apply hmon
      apply ch
      apply hmon
