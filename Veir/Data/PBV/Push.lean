module

public import Veir.Data.PBV.Lemmas
public import Veir.Data.PBV.Mask

/-! # Rewriting a parametric expression into a concrete, single-width one.

`eq_iff` introduces a `setWidth o` at the root of the goal, and the remaining
lemmas push it down towards the leaves, masking the result of every
width-sensitive operation. See `Veir.Data.PBV` for more details.
-/

namespace Veir.Data.PBV

public section

/-! ## Introducing `setWidth o` at the root -/

theorem eq_iff {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩

/-! ## Pushing `setWidth o` towards the leaves — leaves and width changes -/

theorem setWidth_setWidth {w o : Nat} (h : w ≤ o) :
    ∀ {u : Nat} (a : BitVec u),
      (a.setWidth w).setWidth o = a.setWidth o &&& maskOfWidth o w := by
  intro u a
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_mod_pow_of_le h]

/-! ## Width-sensitive arithmetic: mask the result -/

theorem setWidth_add {w o : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w),
      (a + b).setWidth o = (a.setWidth o + b.setWidth o) &&& maskOfWidth o w := by
  intro a b
  refine setWidth_eq_and_maskOfWidth h ?_
  rw [BitVec.toNat_add, BitVec.toNat_setWidth_of_le h, BitVec.toNat_setWidth_of_le h,
    Nat.mod_mod_pow_of_le h, BitVec.toNat_add]

/-- Sign extension fills above the source width `v` with the sign bit,
and then masks to the target width. -/
theorem setWidth_signExtend_eq_and_maskOfWidth {t v o : Nat} (hvo : v ≤ o) :
    ∀ (a : BitVec v),
      (a.signExtend t).setWidth o
        = ((a.setWidth o) ||| (cond a.msb (~~~(maskOfWidth o v)) 0#o)) &&& maskOfWidth o t := by
  intro a
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_setWidth, getLsbD_maskOfWidth]
  by_cases hiv : i < v
  · -- Below the source width: the sign fill is masked out.
    have hio : i < o := by lia
    have hmask : (maskOfWidth o v)[i] = true := by
      rw [getElem_maskOfWidth i hio]; simp [hiv]
    cases hmsb : a.msb <;> grind
  · -- At or above the source width: `a` has no bit here, so the result is the sign bit.
    rw [BitVec.getLsbD_of_ge a i (by lia)]
    cases hmsb : a.msb <;>
      simp [hiv, getLsbD_maskOfWidth, Bool.and_comm]

/-! ### The sign bit: a test against the mask's top bit -/

/-- `a.msb` can be implemented by masking the sign bit,
which are definitions the bitblaster can see. -/
theorem msb_eq_and_signBitOfMask_maskOfWidth_ne_zero {w o : Nat} (h : w ≤ o) :
    ∀ (a : BitVec w),
      a.msb = (((a.setWidth o) &&& signBitOfMask (maskOfWidth o w)) != 0#o) := by
  intro a
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · -- `BitVec 0` has no bits, so both sides are `false`.
    rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_of_ge _ _ (by lia)]
    simp
  · rw [signBitOfMask_maskOfWidth_eq_twoPow_of_pos h hw,
      BitVec.and_twoPow, BitVec.getLsbD_setWidth,
      BitVec.msb_eq_getLsbD_last]
    have hlt : w - 1 < o := by lia
    simp only [hlt, decide_true, Bool.true_and]
    cases a.getLsbD (w - 1)
    · simp
    · simp [BitVec.twoPow_ne_zero hlt]
