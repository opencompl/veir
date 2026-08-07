module

public import Veir.Data.PBV.BitVec
public import Veir.Data.PBV.Mask

namespace Veir.Data.PBV

public section

theorem eq_iff {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩

theorem setWidth_add {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  -- intro a b
  -- refine setWidth_eq_and_maskOfWidth h ?_
  -- rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
  --   Nat.mod_two_pow_mod_two_pow_of_le' h, BitVec.toNat_add]
  sorry

theorem setWidth_setWidth {w o : Nat} (h : w ≤ o) :
    ∀ {u : Nat} (a : BitVec u),
      (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  -- intro u a
  -- refine setWidth_eq_and_maskOfWidth h ?_
  -- rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_two_pow_mod_two_pow_of_le' h]
  sorry
