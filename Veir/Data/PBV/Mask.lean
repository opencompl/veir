module

public import Veir.Data.PBV.Lemmas

/-! # Masks as bitvector variables constrained by `m &&& (m + 1) = 0`.

A width `w` is represented by the mask `2^w - 1` of the blast width, and the
constraint `m &&& (m + 1) = 0` is the only fact about that mask the bitblaster
is given. See `Veir.Data.PBV` for the pipeline this step belongs to.
-/

namespace Veir.Data.PBV

public section

/-- `maskOfWidth o w : BitVec o` has its low `w` bits set. -/
def maskOfWidth (o w : Nat) : BitVec o := BitVec.ofNat o (2 ^ w - 1)

/-- `IsMask` encodes `m = 2^k - 1` for some `k : Nat` in terms of bitvector
operations removing the dependency on `k` and allowing it to be bitblasted. -/
def IsMask {o : Nat} (m : BitVec o) : Prop := m &&& (m + 1#o) = 0#o

theorem toNat_maskOfWidth {o w : Nat} (h : w ≤ o) :
    (maskOfWidth o w).toNat = 2 ^ w - 1 := by
  rw [maskOfWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have h1 : 2 ^ w ≤ 2 ^ o := Nat.pow_le_pow_right (by lia) h
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  lia

/-- Soundness: every real mask satisfies the constraint. -/
theorem isMask_maskOfWidth {o w : Nat} :
    IsMask (maskOfWidth o w) := by
  simp [IsMask, maskOfWidth, BitVec.ofNat_add_ofNat, ← BitVec.ofNat_and,
    Nat.sub_add_cancel Nat.one_le_two_pow, Nat.and_comm (2 ^ w - 1),
    Nat.and_two_pow_sub_one_eq_mod]

/-- The mask constraint: the only fact about `m` surviving abstraction. -/
theorem isMask_of_eq_maskOfWidth {o w : Nat} {m : BitVec o}
    (hm : m = maskOfWidth o w) : IsMask m := by
  subst hm
  exact isMask_maskOfWidth

theorem maskOfWidth_lt_maskOfWidth {o w₁ w₂ : Nat} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (h : w₁ < w₂) : maskOfWidth o w₁ < maskOfWidth o w₂ := by
  rw [BitVec.lt_def, toNat_maskOfWidth h₁, toNat_maskOfWidth h₂]
  have hlt : 2 ^ w₁ < 2 ^ w₂ := Nat.pow_lt_pow_right (by omega) h
  have : 0 < 2 ^ w₁ := Nat.two_pow_pos w₁
  omega

/-- Strict width order becomes strict mask order. -/
theorem mask_lt_mask {o w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂)
    (hw : w₁ < w₂) : m₁ < m₂ := by
  subst hm₁; subst hm₂
  exact maskOfWidth_lt_maskOfWidth h₁ h₂ hw

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

theorem getLsbD_maskOfWidth {o w : Nat} (i : Nat) :
    (maskOfWidth o w).getLsbD i = (decide (i < w) && decide (i < o)) := by
  rw [maskOfWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  exact Bool.and_comm _ _

theorem getElem_maskOfWidth {o w : Nat} (i : Nat) (hi : i < o) :
    (maskOfWidth o w)[i] = decide (i < w) := by
  rw [← BitVec.getLsbD_eq_getElem, getLsbD_maskOfWidth]
  simp [hi]

theorem maskOfWidth_zero (o : Nat) : maskOfWidth o 0 = 0#o := by
  simp [maskOfWidth]

/-! ## The sign bit helpers -/

/-- `signBitOfMask m` keeps only the top bit of the mask `m`, i.e. the sign bit of the width `m`
represents. -/
@[expose] def signBitOfMask {o : Nat} (m : BitVec o) := m - (m >>> 1)

theorem toNat_signBitOfMask_maskOfWidth {o w : Nat} (h : w ≤ o) :
    (signBitOfMask (maskOfWidth o w)).toNat = 2 ^ w - 2 ^ (w - 1) := by
  rw [signBitOfMask, BitVec.toNat_sub_of_le (BitVec.ushiftRight_one_le _),
    BitVec.toNat_ushiftRight,
    toNat_maskOfWidth h, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      rw [Nat.pow_succ, Nat.add_sub_cancel]
      omega
    have h3 : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
    omega

theorem signBitOfMask_maskOfWidth_of_pos {o w : Nat} (h : w ≤ o) (hw : 0 < w) :
    signBitOfMask (maskOfWidth o w) = BitVec.twoPow o (w - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_signBitOfMask_maskOfWidth h, BitVec.toNat_twoPow,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega : w - 1 < o))]
  have h2 : 2 ^ w = 2 * 2 ^ (w - 1) := by
    obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
    rw [Nat.pow_succ, Nat.add_sub_cancel]
    omega
  omega
