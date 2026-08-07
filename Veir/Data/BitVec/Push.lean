module

public import Veir.Data.BitVec.Mask

namespace Veir.Data.BitVec

public section

/-- Widening is injective, which makes stage 1 of the translation reversible. -/
theorem setWidth_inj {w o : Nat} (h : w ≤ o) {a b : BitVec w}
    (hab : a.setWidth o = b.setWidth o) : a = b := by
  -- apply BitVec.eq_of_toNat_eq
  -- have := congrArg BitVec.toNat hab
  -- rwa [toNat_setWidth_of_le h, toNat_setWidth_of_le h] at this
  sorry

theorem pbv_eq_iff {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => setWidth_inj h hab⟩

theorem pbv_setWidth_add {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  -- intro a b
  -- refine setWidth_eq_and_maskOfWidth h ?_
  -- rw [BitVec.toNat_add, toNat_setWidth_of_le h, toNat_setWidth_of_le h,
  --   mod_two_pow_mod_two_pow_of_le' h, BitVec.toNat_add]
  sorry

theorem pbv_setWidth_setWidth {w o : Nat} (h : w ≤ o) :
    ∀ {u : Nat} (a : BitVec u),
      (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  -- intro u a
  -- refine setWidth_eq_and_maskOfWidth h ?_
  -- rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, mod_two_pow_mod_two_pow_of_le' h]
  sorry
