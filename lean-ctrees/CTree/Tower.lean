module

import Std.Internal.Order.Basic
public import CTree.Order

/-!
Coinductive predicates up-to companion based on tower induction
This implements some of the theories of https://doi.org/10.1007/978-3-319-57418-9_17
-/

public section

namespace Tower

open Lean.Order

variable {α} [L: CompleteLattice α] (f : α → α)

/-- Tower induction -/
inductive Tower : α → Prop where
  | chain {x} (h : Tower x) : Tower (f x)
  | inf (P : α → Prop) : (∀ x, P x → Tower x) → Tower (inf P)

/-- An element of a tower -/
structure Chain where
  elem : α
  hTower : Tower f elem

attribute [coe] Chain.elem

/-- Tower-based definition of the companion -/
noncomputable def cpn (x : α) : α := inf (fun y : α => Tower f y ∧ x ⊑ y)

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

theorem le_x_cpn_x : ∀ (x : α), x ⊑ cpn f x := by
  grind [cpn, inf_spec]

theorem cpn_cpn : ∀ x, cpn f (cpn f x) = cpn f x := by
  intros x
  apply PartialOrder.rel_antisymm
  · apply inf_le
    constructor <;> try apply PartialOrder.rel_refl
    apply Tower.inf
    grind
  · apply cpn_mon
    apply le_x_cpn_x

theorem tower_iff_cpn : ∀ x, Tower f x ↔ cpn f x = x := by
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
    apply Tower.inf
    grind

theorem cpn_f_cpn : ∀ x, f (cpn f x) = cpn f (f (cpn f x)) := by
  intros x
  apply PartialOrder.rel_antisymm
  · apply le_inf
    intros y h
    grind
  · apply inf_le
    constructor
    · apply Tower.chain
      rw [tower_iff_cpn]
      apply cpn_cpn
    · rfl

@[expose]
def InfClosed (P : α → Prop) : Prop :=
  ∀ M : α → Prop, (∀ m, M m → P m) -> P (inf M)

theorem tower_ind_cpn : ∀ (P : α → Prop),
    InfClosed P →
    (∀ x, P (cpn f x) → P (f (cpn f x))) →
    ∀ x, P (cpn f x) := by
  intros P h h' x
  unfold InfClosed at h
  apply h
  intros y h''
  have h''' := h''.1
  clear x h''
  induction h'''
  case chain z h1 ih =>
    rw [tower_iff_cpn] at h1
    rw [<-h1]
    apply h'
    rw [h1]
    apply ih
  case inf Q h'' ih =>
    apply h
    exact ih

/-- The main induction principle for chains -/
theorem tower_ind : ∀ (P : α → Prop),
    InfClosed P →
    (∀ x : Chain f, P x.elem → P (f x.elem)) →
    ∀ x : Chain f, P x.elem := by
  intros P h h' x
  unfold InfClosed at h
  rcases x with ⟨x, ht⟩
  simp only
  induction ht
  case chain y ht ih =>
    apply (h' ⟨y, ht⟩)
    apply ih
  case inf Q h'' ih =>
    apply h
    exact ih

noncomputable def bot : α := L.sup (fun _ => False)

/-- Companion-based definition of greatest fixpoint -/
noncomputable abbrev gfp : α := cpn f bot

/-- Standard definition of greatest fixpoint -/
noncomputable def gfp' : α := L.sup (fun x => x ⊑ f x)

theorem bot_le : ∀ x : α, Tower.bot ⊑ x := by
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
theorem gfp_eq_gfp' : monotone f → gfp f = gfp' f := by
  intros hmon
  apply PartialOrder.rel_antisymm
  · apply le_sup
    rw [cpn_f_cpn (f := f) (x := Tower.bot)]
    apply cpn_mon
    apply Tower.bot_le
  · apply tower_ind_cpn
    · unfold InfClosed
      intros M h'
      apply le_inf
      apply h'
    · intros y ch
      rw [<-f_gfp']
      apply hmon
      apply ch
      apply hmon
