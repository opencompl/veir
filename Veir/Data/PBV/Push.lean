module

public import Veir.Data.PBV.BitVec
public import Veir.Data.PBV.Mask

namespace Veir.Data.PBV


public section

/-! ## Helpers -/

/-- Reduction mod `2^o` is absorbed by the later reduction mod the smaller `2^w`. -/
theorem mod_two_pow_mod_two_pow_of_le' {w o : Nat} (h : w ≤ o) (n : Nat) :
    n % 2 ^ o % 2 ^ w = n % 2 ^ w :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

/-- Widening and truncating back is the identity: the round trip `pbv_var_elim` relies on. -/
theorem setWidth_setWidth_eq_self {w o : Nat} (h : w ≤ o) (x : BitVec w) :
    (x.setWidth o).setWidth w = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le h, Nat.mod_eq_of_lt x.isLt]

/-! ## Stage 1: lifting atoms to the blast width -/

theorem eq_iff {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩

/-! ## Stage 2: pushing `setWidth o` towards the leaves — leaves and width changes -/

theorem setWidth_setWidth {w o : Nat} (h : w ≤ o) :
    ∀ {u : Nat} (a : BitVec u),
      (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  intro u a
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, mod_two_pow_mod_two_pow_of_le' h]

/-! ### Width-sensitive arithmetic: mask the result -/

theorem setWidth_add {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    mod_two_pow_mod_two_pow_of_le' h, BitVec.toNat_add]
