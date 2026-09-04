module

public import Veir.Data.PBV.Lemmas

/-! # Masks as bitvector variables constrained by `m &&& (m + 1) = 0`.

A width `w` is represented by the mask `2^w - 1` of the blast width, and it is
encoded as a bitvector constraint `m &&& (m + 1) = 0` which the bitblaster
can reason about. Other relations between bitwidths are encoded as bitvector
inequalities and equalities.
-/

namespace Veir.Data.PBV

public section

/-- `maskOfWidth o w : BitVec o` has its low `w` bits set. -/
def maskOfWidth (o w : Nat) : BitVec o := BitVec.ofNat o (2 ^ w - 1)

theorem toNat_maskOfWidth {o w : Nat} (h : w ≤ o) :
    (maskOfWidth o w).toNat = 2 ^ w - 1 := by
  rw [maskOfWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have h1 : 2 ^ w ≤ 2 ^ o := Nat.pow_le_pow_right (by lia) h
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  lia

/-- The mask constraint: the only fact about `m` surviving abstraction. This
encodes `m = 2^k - 1` for some `k : Nat` in terms of bitvector operations
removing the dependency on `k` and allowing it to be bitblasted. -/
theorem maskOfWidth_and_add_one_eq_zero {o w : Nat} {m : BitVec o}
    (hm : m = maskOfWidth o w) : m &&& (m + 1#o) = 0#o := by
  subst hm
  simp [maskOfWidth, BitVec.ofNat_add_ofNat, ← BitVec.ofNat_and,
    Nat.sub_add_cancel Nat.one_le_two_pow, Nat.and_comm (2 ^ w - 1),
    Nat.and_two_pow_sub_one_eq_mod]

/-- `maskOfWidth` is monotone with respect to unsigned bitvec comparison. -/
theorem maskOfWidth_lt_maskOfWidth {o w₁ w₂ : Nat} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (h : w₁ < w₂) : maskOfWidth o w₁ < maskOfWidth o w₂ := by
  rw [BitVec.lt_def, toNat_maskOfWidth h₁, toNat_maskOfWidth h₂]
  have hlt : 2 ^ w₁ < 2 ^ w₂ := Nat.pow_lt_pow_right (by lia) (by lia)
  have : 0 < 2 ^ w₁ := by grind
  lia

/-- Strict width order becomes strict mask order. -/
theorem mask_lt_mask {o w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂)
    (hw : w₁ < w₂) : m₁ < m₂ := by
  grind only [maskOfWidth_lt_maskOfWidth]

/-- ANDing with `maskOfWidth o w` keeps exactly the low `w` bits. -/
theorem toNat_and_maskOfWidth {o w : Nat} (h : w ≤ o) (x : BitVec o) :
    (x &&& maskOfWidth o w).toNat = x.toNat % 2 ^ w := by
  rw [BitVec.toNat_and, toNat_maskOfWidth h, Nat.and_two_pow_sub_one_eq_mod]

/-- Introduction rule for every push lemma: it suffices that `b = a` mod `2^w`. -/
theorem setWidth_eq_and_maskOfWidth {o w : Nat} {a : BitVec w} {b : BitVec o}
    (h : w ≤ o) (hab : b.toNat % 2 ^ w = a.toNat) :
    a.setWidth o = b &&& maskOfWidth o w := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_maskOfWidth h, BitVec.toNat_setWidth_of_le h, hab]

/-- The `i`th bit of `maskOfWidth o w` is enabled iff
the index `i` is inbounds of `o` and `w`. -/
@[simp] theorem getLsbD_maskOfWidth {o w : Nat} (i : Nat) :
    (maskOfWidth o w).getLsbD i = (decide (i < w) && decide (i < o)) := by
  rw [maskOfWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  grind only

/-- The `i`th bit of `maskOfWidth o w` is enabled iff
the index `i` is inbounds of `w`. -/
@[simp] theorem getElem_maskOfWidth {o w : Nat} (i : Nat) (hi : i < o) :
    (maskOfWidth o w)[i] = decide (i < w) := by
  rw [← BitVec.getLsbD_eq_getElem, getLsbD_maskOfWidth]
  grind only

/-- Mask of width 0 is the zero bitvector. -/
@[simp] theorem maskOfWidth_zero (o : Nat) : maskOfWidth o 0 = 0#o := by
  simp [maskOfWidth]

/-! ## The sign bit helpers -/

/-- `signBitOfMask m` keeps only the top bit of the mask `m`.
This is used to extract the sign bit of a width `o` bitvector. -/
def signBitOfMask {o : Nat} (m : BitVec o) := m - (m >>> 1)

theorem signBitOfMask_eq {o : Nat} (m : BitVec o) :
    signBitOfMask m = m - (m >>> 1) := by
  unfold signBitOfMask
  rfl

/-- The zero bitvector, which is the mask of width `0`, has no sign bit. -/
@[simp] theorem signBitOfMask_zero {o : Nat} : signBitOfMask (0#o) = 0#o := by
  simp [signBitOfMask]

/-- The `Nat` denotation of `signBitOfMask` of a mask of width `w`
is given by `2^w` minus `2^(w - 1)`. -/
theorem toNat_signBitOfMask_maskOfWidth {o w : Nat} (h : w ≤ o) :
    (signBitOfMask (maskOfWidth o w)).toNat = 2 ^ w - 2 ^ (w - 1) := by
  rw [signBitOfMask, BitVec.toNat_sub_of_le (BitVec.ushiftRight_one_le _),
    BitVec.toNat_ushiftRight,
    toNat_maskOfWidth h, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by lia⟩
      lia
    have h3 : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
    lia

/-- The sign bit of a mask of non-zero width `w` is the bitvector `2^(w - 1)`. -/
@[simp] theorem signBitOfMask_maskOfWidth_eq_twoPow_of_pos {o w : Nat} (h : w ≤ o) (hw : 0 < w) :
    signBitOfMask (maskOfWidth o w) = BitVec.twoPow o (w - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_signBitOfMask_maskOfWidth h, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by lia) (by lia : w - 1 < o))]
  have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by lia⟩
    lia
  lia
