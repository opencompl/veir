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

theorem inf_iff_binary_rel (P : (α → β → Prop) → Prop) : ∀ x y, inf P x y ↔ ∀ R, P R → R x y := by
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

end Tower
