module
/-! # `Nat` and `BitVec` lemmas used by the parametric-bitvector translation.

These mention nothing specific to `PBV`.
-/

public section

namespace Nat

/-- Reduction mod `2^o` is absorbed by the later reduction mod the smaller `2^w`. -/
theorem mod_two_pow_mod_two_pow_of_le {w o : Nat} (h : w ≤ o) (n : Nat) :
    n % 2 ^ o % 2 ^ w = n % 2 ^ w :=
  Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

end Nat

namespace BitVec

/-- Widening is injective --/
theorem setWidth_inj {w o : Nat} (h : w ≤ o) {a b : BitVec w}
    (hab : a.setWidth o = b.setWidth o) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_eq] at hab
  repeat rw [BitVec.toNat_setWidth_of_le h] at hab
  exact hab

/-- Widening and truncating back is the identity: the round trip `var_elim` relies on. -/
theorem setWidth_setWidth_eq_self_of_le {w o : Nat} (h : w ≤ o) (x : BitVec w) :
    (x.setWidth o).setWidth w = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth_of_le h, Nat.mod_eq_of_lt x.isLt]

theorem ushiftRight_one_le {o : Nat} (m : BitVec o) : m >>> 1 ≤ m := by
  rw [BitVec.le_def, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _

theorem twoPow_ne_zero {o k : Nat} (h : k < o) : BitVec.twoPow o k ≠ 0#o := by
  intro hcontra
  have hn := congrArg BitVec.toNat hcontra
  rw [BitVec.toNat_twoPow, BitVec.toNat_zero,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) h)] at hn
  exact absurd hn (Nat.ne_of_gt (Nat.two_pow_pos k))

end BitVec
