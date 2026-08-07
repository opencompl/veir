module
/-! # `BitVec` lemmas used by the parametric-bitvector translation.

These mention nothing specific to `PBV`, so they are stated in the upstream namespace and
are candidates for upstreaming.
-/

public section

namespace BitVec

/-- Widening is injective, which makes stage 1 of the translation reversible. -/
theorem setWidth_inj {w o : Nat} (h : w ≤ o) {a b : BitVec w}
    (hab : a.setWidth o = b.setWidth o) : a = b := by
  -- apply BitVec.eq_of_toNat_eq
  -- have := congrArg BitVec.toNat hab
  -- rwa [toNat_setWidth_of_le h, toNat_setWidth_of_le h] at this
  sorry

end BitVec
