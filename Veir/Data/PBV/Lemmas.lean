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

/-! ### Leading and trailing zeros -/

theorem toNat_clz_zero : (0#w).clz.toNat = w := by
  rw [BitVec.clz_eq_iff_eq_zero.mpr rfl, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt Nat.lt_two_pow_self]

theorem toNat_ctz_zero : (0#w).ctz.toNat = w := by
  rw [BitVec.ctz_eq_reverse_clz, BitVec.reverse_eq_zero_iff.mpr rfl, toNat_clz_zero]

/-- Zero-extending a nonzero bitvector keeps it nonzero. -/
theorem setWidth_ne_zero_of_le {a : BitVec w} (h : w ≤ o) (ha : a ≠ 0#w) :
    a.setWidth o ≠ 0#o := by
  intro hz
  apply ha
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat hz
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) h))] at this
  simpa using this

/-- The leading zeros of a nonzero bitvector, in terms of the position of its highest set bit. -/
theorem clz_eq_log2 {a : BitVec w} (ha : a ≠ 0#w) : a.clz.toNat = w - 1 - a.toNat.log2 := by
  have hw : 0 < w := by
    rcases w with _ | w
    · exact absurd (BitVec.eq_nil a) ha
    · grind
  have hlt : a.clz.toNat < w := by
    have := (BitVec.clz_lt_iff_ne_zero (x := a)).2 ha
    simpa [BitVec.lt_def, Nat.mod_eq_of_lt (Nat.lt_two_pow_self)] using this
  have h_le := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero hw ha
  have h_lt := BitVec.toNat_lt_two_pow_sub_clz (x := a)
  have : a.toNat.log2 = w - 1 - a.clz.toNat :=
    (Nat.log2_eq_iff (by grind)).mpr ⟨h_le, by grind⟩
  grind

theorem log2_toNat_of_lt_two_pow {a : BitVec w} (ha : a ≠ 0#w) (h : a.toNat < 2^o) :
    a.toNat.log2 < o := by
  have : 0 < a.toNat := by grind
  rw [Nat.log2_lt (by grind)]
  exact h

theorem toNat_clz_setWidth_add_one {a : BitVec w} (h : w ≤ o) :
    (BitVec.setWidth (o + 1) a).clz.toNat = (BitVec.setWidth o a).clz.toNat + 1 := by
  by_cases h' : a = 0#w
  · subst h'
    rw [BitVec.setWidth_zero, BitVec.setWidth_zero, toNat_clz_zero, toNat_clz_zero]
  · have a_lt : a.toNat < 2 ^ o :=
      Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) h)
    have hlog := log2_toNat_of_lt_two_pow h' a_lt
    rw [clz_eq_log2 (setWidth_ne_zero_of_le (by omega) h'),
      clz_eq_log2 (setWidth_ne_zero_of_le h h')]
    simp only [BitVec.toNat_setWidth, Nat.mod_eq_of_lt a_lt,
      Nat.mod_eq_of_lt (Nat.lt_trans a_lt (Nat.pow_lt_pow_succ (by decide)))]
    omega

/-- Zero-extending by `o - w` bits adds `o - w` leading zeros. -/
theorem toNat_clz_setWidth {o w : Nat} (a : BitVec w) (h : w ≤ o) :
    (a.setWidth o).clz.toNat = a.clz.toNat + (o - w) := by
  induction o
  case zero =>
    have : w = 0 := by grind
    simp only [BitVec.clz, Nat.zero_le, Nat.sub_eq_zero_of_le, BitVec.clzAuxRec, Std.le_refl,
      BitVec.getLsbD_of_ge, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat, Nat.pow_zero,
      Nat.mod_succ, this, Nat.add_zero]
  case succ o' ih =>
    rcases Nat.lt_or_eq_of_le h
    case inl h' =>
      have w_le_o : w ≤ o' := by apply Nat.le_of_lt_add_one h'
      rw [toNat_clz_setWidth_add_one w_le_o, ih w_le_o, Nat.add_assoc, Nat.sub_add_comm w_le_o]
    case inr h' =>
      subst h'
      simp only [BitVec.setWidth_eq, Nat.sub_self, Nat.add_zero]

/-- Zero-extending a nonzero bitvector does not change its trailing zeros. -/
theorem toNat_ctz_setWidth_of_ne_zero {a : BitVec w} (h : w ≤ o) (ha : a ≠ 0#w) :
    (a.setWidth o).ctz.toNat = a.ctz.toNat := by
  have ha' := setWidth_ne_zero_of_le h ha
  have hb : ∀ i, (a.setWidth o).getLsbD i = a.getLsbD i := by
    intro i
    rw [BitVec.getLsbD_setWidth]
    by_cases hi : i < o
    · simp [hi]
    · simp [hi, BitVec.getLsbD_of_ge a i (by omega)]
  have h1 := BitVec.getLsbD_true_ctz_of_ne_zero ha
  have h2 := BitVec.getLsbD_true_ctz_of_ne_zero ha'
  apply Nat.le_antisymm
  · apply Nat.le_of_not_lt
    intro hlt
    have := BitVec.getLsbD_false_of_lt_ctz hlt
    rw [hb] at this
    simp_all
  · apply Nat.le_of_not_lt
    intro hlt
    have := BitVec.getLsbD_false_of_lt_ctz hlt
    rw [← hb] at this
    simp_all

end BitVec
