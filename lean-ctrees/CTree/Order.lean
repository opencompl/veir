module

import Std.Internal.Order.Basic


public section

/-!
Results around order theory useful for tower induction
-/

open Lean.Order

namespace Tower

scoped instance : PartialOrder Prop where
  rel := fun x y => x → y
  rel_refl := by simp
  rel_trans := by grind
  rel_antisymm := by grind

scoped instance : CompleteLattice Prop where
  has_sup c := ⟨(exists x, x ∧ c x), by
    unfold is_sup
    intros y
    constructor
    · intros h z h' h''
      apply h
      exists z
    · intros h h'
      rcases h' with ⟨x, hx, hcx⟩
      apply (h x hcx hx)⟩

variable {α : Type u1} {β : Type u2} {γ : Type u3}

theorem le_def_binary_rel (R R' : α → β → Prop) :
    R ⊑ R' ↔ forall x y, R x y → R' x y := by
  simp [PartialOrder.rel]

theorem le_def_ternary_rel (R R' : α → β → γ → Prop) :
    R ⊑ R' ↔ forall x y z, R x y z → R' x y z := by
  simp [PartialOrder.rel]

theorem inf_iff_binary_rel (P : (α → β → Prop) → Prop) :
    ∀ x y, inf P x y ↔ ∀ R, P R → R x y := by
  intros x y
  constructor
  · intros hinf R h
    have hle : PartialOrder.rel (inf P) R := by
      apply inf_le
      apply h
    apply hle
    apply hinf
  · intros h
    have hle : PartialOrder.rel (fun x y => ∀ R, P R → R x y) (inf P) := by
      apply le_inf
      intros R h
      simp only [PartialOrder.rel]
      grind
    apply hle
    apply h

theorem inf_iff_ternary_rel (P : (α → β → γ → Prop) → Prop) :
    ∀ x y z, inf P x y z ↔ ∀ R, P R → R x y z := by
  intros x y z
  constructor
  · intros hinf R h
    have hle : PartialOrder.rel (inf P) R := by
      apply inf_le
      apply h
    apply hle
    apply hinf
  · intros h
    have hle : PartialOrder.rel (fun x y z => ∀ R, P R → R x y z) (inf P) := by
      apply le_inf
      intros R h
      simp only [PartialOrder.rel]
      grind
    apply hle
    apply h

end Tower
