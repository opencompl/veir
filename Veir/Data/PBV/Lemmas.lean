module
/-! # `Nat` and `BitVec` lemmas used by the parametric-bitvector translation.

These mention nothing specific to `PBV`.
-/

public section

namespace Nat

/-- Reduction mod `x^o` is absorbed by the later reduction mod the smaller `x^w`. -/
theorem mod_mod_pow_of_le {x w o : Nat} (h : w ≤ o) (n : Nat) :
    n % x ^ o % x ^ w = n % x ^ w :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow x h)

/-- A power of `x` modulo a smaller power of `x` is zero. -/
theorem pow_mod_pow_of_le {x w o : Nat} (h : w ≤ o) :
    x ^ o % x ^ w = 0 := by
  cases h
  · rw [mod_self]
  · grind [Nat.mod_eq_zero_of_dvd, Nat.pow_dvd_pow]

/-- Modulo `2 ^ w`, subtracting `n` from a larger power of two `2 ^ o` is the
same as subtracting it from `2 ^ w` -/
theorem two_pow_sub_mod_of_le {w o n : Nat} (h : w ≤ o) (hn : n ≤ 2 ^ w) :
    (2 ^ o - n) % 2 ^ w = (2 ^ w - n) % 2 ^ w := by
  have h0 : (2 ^ o - 2 ^ w) % 2 ^ w = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (by rw [pow_mod_pow_of_le h, Nat.mod_self])
  have : (2 ^ o - n) = (2 ^ w - n + 2 ^ o - 2^w) := by grind[Nat.mul_sub_one]
  simp only [this, Nat.add_sub_assoc (by apply Nat.pow_le_pow_right (n := 2) (by grind) h),
    add_mod, h0, Nat.add_zero, Nat.dvd_refl, mod_mod_of_dvd]

end Nat

namespace BitVec

/-- Widening is injective --/
theorem setWidth_inj {w o : Nat} (h : w ≤ o) {a b : BitVec w}
    (hab : a.setWidth o = b.setWidth o) : a = b := by
  simpa [h] using congrArg (BitVec.setWidth w) hab

/-- Shifting right by one can only decrease a bitvector. -/
theorem ushiftRight_one_le {o : Nat} (m : BitVec o) : m >>> 1 ≤ m := by
  rw [le_def, toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

/-- A power of two that is in bounds of the width is a non-zero bitvector. -/
theorem twoPow_ne_zero {o k : Nat} (h : k < o) : twoPow o k ≠ 0#o := by
  intro hcontra
  have hn := congrArg BitVec.toNat hcontra
  rw [toNat_twoPow, toNat_zero,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by lia) h)] at hn
  exact absurd hn (Nat.ne_of_gt (Nat.two_pow_pos k))

end BitVec
