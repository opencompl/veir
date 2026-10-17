module

import Std.Internal.Order.Basic


public section

open Lean.Order

instance : PartialOrder Prop where
  rel := fun x y => x → y
  rel_refl := by simp
  rel_trans := by grind
  rel_antisymm := by grind

instance : CompleteLattice Prop where
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

theorem inf_binary_rel (P : (α → β → Prop) → Prop) : forall x y, inf P x y ↔ forall R, P R → R x y := by
  intros x y
  constructor
  · intros hinf R h
    have hle : Lean.Order.PartialOrder.rel (inf P) R := by
      apply inf_le
      apply h
    apply hle
    apply hinf
  · intros h
    have hle : Lean.Order.PartialOrder.rel (fun x y => forall R, P R → R x y) (inf P) := by
      apply le_inf
      intros R h
      simp only [PartialOrder.rel]
      grind
    apply hle
    apply h
