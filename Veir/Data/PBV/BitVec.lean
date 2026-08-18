module
/-! # `BitVec` lemmas used by the parametric-bitvector translation.

These mention nothing specific to `PBV`
-/

public section

namespace BitVec

/-- Widening is injective --/
theorem setWidth_inj {w o : Nat} (h : w ≤ o) {a b : BitVec w}
    (hab : a.setWidth o = b.setWidth o) : a = b := by
  grind [BitVec.eq_of_toNat_eq, BitVec.toNat_setWidth_of_le]

end BitVec
