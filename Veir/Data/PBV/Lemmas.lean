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

end Nat

namespace BitVec

/-- Widening is injective --/
theorem setWidth_inj {w o : Nat} (h : w ≤ o) {a b : BitVec w}
    (hab : a.setWidth o = b.setWidth o) : a = b := by
  simpa [h] using congrArg (BitVec.setWidth w) hab

/-- Widening and truncating back is the identity. -/
theorem setWidth_setWidth_eq_self_of_le {w o : Nat} (h : w ≤ o) (x : BitVec w) :
    (x.setWidth o).setWidth w = x := by
  apply eq_of_toNat_eq
  rw [toNat_setWidth, toNat_setWidth_of_le h, Nat.mod_eq_of_lt x.isLt]

end BitVec
