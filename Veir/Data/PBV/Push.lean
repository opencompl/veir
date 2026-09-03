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


/-- Introducing `setWidth o` at the root.
`o` must be the first binder, since it should be bound to the concrete width
being used in the proof..
 -/
theorem eq_iff (o : Nat) {w : Nat} (h : w ≤ o) :
    ∀ (a b : BitVec w), (a = b) = (a.setWidth o = b.setWidth o) := by
  intro a b
  apply propext
  exact ⟨fun hab => hab ▸ rfl, fun hab => BitVec.setWidth_inj h hab⟩

/-! ## Translating `Nat` width relations and arithmetic into mask operations -/

/-- `<` on the widths translates to `<` on the masks. -/
theorem lt_eq_lt_of_eq_maskOfWidth {o w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂)
    (hw₁w₂ : w₁ < w₂) : (m₁ < m₂) := by
  subst m₁ m₂
  rw [BitVec.lt_def, toNat_maskOfWidth h₁, toNat_maskOfWidth h₂,
      Nat.sub_lt_sub_iff_right (by grind), Nat.pow_lt_pow_iff_right (by grind)]
  exact hw₁w₂

/-- Adding widths becomes multiplying masks: `2^(w₁ + w₂) - 1` is
`2^w₁ * 2^w₂ - 1`, written in terms of the masks `m₁` and `m₂`. -/
theorem maskOfWidth_add_eq_mul_of_maskOfWidth {o w₁ w₂ : Nat} {m₁ m₂ : BitVec o}
    (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o) (h₁₂ : w₁ + w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂) :
    maskOfWidth o (w₁ + w₂) = (m₁ + 1#o) * (m₂ + 1#o) - 1#o := by
  cases o
  · simp [hm₁, hm₂, maskOfWidth_zero_eq_zero]
  · rw [hm₁, maskOfWidth_add_one_eq_twoPow h₁, hm₂, maskOfWidth_add_one_eq_twoPow h₂,
      BitVec.twoPow_mul_twoPow_eq]
    apply maskOfWidth_eq_twoPow_sub_one h₁₂

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

/-- `a ++ b` shifts `a` up by the width of `b`; at the blast width that shift
is a multiplication by `2^w = maskOfWidth o w + 1`, and the two halves no
longer overlap, so they can be recombined with `|||`. -/
theorem setWidth_append_eq_or_mul_maskOfWidth_add_one {w o : Nat} (h : w ≤ o) :
    ∀ {v : Nat} (a : BitVec v) (b : BitVec w), v + w ≤ o →
      (a ++ b).setWidth o
        = ((a.setWidth o) * (maskOfWidth o w + 1#o)) ||| b.setWidth o := by
  intro v a b hvw
  have hv : v ≤ o := by lia
  have ha : a.toNat * 2 ^ w < 2 ^ o := by
    calc a.toNat * 2 ^ w < 2 ^ v * 2 ^ w :=
          Nat.mul_lt_mul_of_lt_of_le a.isLt (Nat.le_refl _) (Nat.two_pow_pos w)
      _ = 2 ^ (v + w) := (Nat.pow_add 2 v w).symm
      _ ≤ 2 ^ o := Nat.pow_le_pow_right (by lia) hvw
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth_of_le hvw, BitVec.toNat_or, BitVec.toNat_append,
      BitVec.toNat_setWidth_of_le h, BitVec.toNat_mul, BitVec.toNat_add,
      BitVec.toNat_setWidth_of_le hv, toNat_maskOfWidth h, BitVec.toNat_ofNat]
  congr 1
  have h2 : (2 ^ w - 1 + 1 % 2 ^ o) % 2 ^ o = 2 ^ w % 2 ^ o := by
    rw [Nat.add_mod_mod]
    congr 1
    have := Nat.two_pow_pos w
    lia
  rw [h2, Nat.mul_mod_mod, Nat.shiftLeft_eq, Nat.mod_eq_of_lt ha]

/-! ### The sign bit: a test against the mask's top bit -/

/-- `a.msb` can be implemented by masking the sign bit,
which are definitions the bitblaster can see. -/
theorem msb_eq_and_signBitOfMask_maskOfWidth_ne_zero (o : Nat) {w : Nat} (h : w ≤ o) :
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
