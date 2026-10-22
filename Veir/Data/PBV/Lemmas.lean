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
same as subtracting it from `2 ^ w`. -/
theorem two_pow_sub_mod_of_le {w o n : Nat} (h : w ≤ o) (hn : n ≤ 2 ^ w) :
    (2 ^ o - n) % 2 ^ w = (2 ^ w - n) % 2 ^ w := by
  have h0 : (2 ^ o - 2 ^ w) % 2 ^ w = 0 :=
    Nat.sub_mod_eq_zero_of_mod_eq (by rw [pow_mod_pow_of_le h, Nat.mod_self])
  have : (2 ^ o - n) = (2 ^ w - n + 2 ^ o - 2^w) := by grind[Nat.mul_sub_one]
  simp only [this, Nat.add_sub_assoc (by apply Nat.pow_le_pow_right (n := 2) (by grind) h),
    add_mod, h0, Nat.add_zero, Nat.dvd_refl, mod_mod_of_dvd]

/-- The exponent `e` with `2 ^ (e - 1) ≤ t < 2 ^ e` is unique among `e ≥ 1`. -/
theorem eq_of_two_pow_sub_one_le_of_lt {t e₁ e₂ : Nat} (h₁ : 0 < e₁) (h₂ : 0 < e₂)
    (hl₁ : 2 ^ (e₁ - 1) ≤ t) (hu₁ : t < 2 ^ e₁)
    (hl₂ : 2 ^ (e₂ - 1) ≤ t) (hu₂ : t < 2 ^ e₂) :
    e₁ = e₂ := by
  rcases Nat.lt_trichotomy e₁ e₂ with h | h | h
  · have := Nat.pow_le_pow_right (n := 2) (by decide) (show e₁ ≤ e₂ - 1 by lia)
    lia
  · exact h
  · have := Nat.pow_le_pow_right (n := 2) (by decide) (show e₂ ≤ e₁ - 1 by lia)
    lia

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

/-- Widening a bitvector adds the new bits to its leading zeros. -/
theorem toNat_clz_setWidth {o w : Nat} (h : w ≤ o) (a : BitVec w) :
    (a.setWidth o).clz.toNat = a.clz.toNat + (o - w) := by
  by_cases ha : a = 0#w
  · subst ha
    have h1 : (0#w).clz = BitVec.ofNat w w := clz_eq_iff_eq_zero.mpr rfl
    have h2 : (0#o).clz = BitVec.ofNat o o := clz_eq_iff_eq_zero.mpr rfl
    rw [setWidth_zero, h1, h2, toNat_ofNat, toNat_ofNat,
      Nat.mod_eq_of_lt Nat.lt_two_pow_self, Nat.mod_eq_of_lt Nat.lt_two_pow_self]
    lia
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | hw
      · exact absurd of_length_zero ha
      · exact hw
    have ha' : a.setWidth o ≠ 0#o := by
      intro h0
      apply ha
      apply eq_of_toNat_eq
      have := congrArg BitVec.toNat h0
      rw [toNat_setWidth_of_le h] at this
      simpa using this
    have hcw : a.clz.toNat < w := by
      have := clz_lt_iff_ne_zero.mpr ha
      rw [lt_def, natCast_eq_ofNat, toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self] at this
      exact this
    have hco : (a.setWidth o).clz.toNat < o := by
      have := clz_lt_iff_ne_zero.mpr ha'
      rw [lt_def, natCast_eq_ofNat, toNat_ofNat, Nat.mod_eq_of_lt Nat.lt_two_pow_self] at this
      exact this
    have l₁ := two_pow_sub_clz_le_toNat_of_ne_zero hw ha
    have u₁ := toNat_lt_two_pow_sub_clz (x := a)
    have l₂ := two_pow_sub_clz_le_toNat_of_ne_zero (by lia) ha'
    have u₂ := toNat_lt_two_pow_sub_clz (x := a.setWidth o)
    rw [toNat_setWidth_of_le h] at l₂ u₂
    have := Nat.eq_of_two_pow_sub_one_le_of_lt
      (e₁ := w - a.clz.toNat) (e₂ := o - (a.setWidth o).clz.toNat) (by lia) (by lia)
      (by rw [show w - a.clz.toNat - 1 = w - 1 - a.clz.toNat by lia]; exact l₁) u₁
      (by rw [show o - (a.setWidth o).clz.toNat - 1 = o - 1 - (a.setWidth o).clz.toNat by lia]
          exact l₂)
      u₂
    lia

end BitVec
