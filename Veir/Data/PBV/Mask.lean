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

/-- `m.IsMask` holds when `m = 2^k - 1` for some `k`; the only fact the
bitblaster gets about a width mask. -/
def IsMask {o : Nat} (m : BitVec o) : Prop := m &&& (m + 1#o) = 0#o

theorem toNat_maskOfWidth {o w : Nat} (h : w ≤ o) :
    (maskOfWidth o w).toNat = 2 ^ w - 1 := by
  rw [maskOfWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have h1 : 2 ^ w ≤ 2 ^ o := Nat.pow_le_pow_right (by omega) h
  have h2 : 0 < 2 ^ w := Nat.two_pow_pos w
  grind

/-- Soundness: every real mask satisfies the constraint. -/
theorem isMask_maskOfWidth {o w : Nat} (_h : w <= o)
  : IsMask (maskOfWidth o w) := by
  simp [IsMask, maskOfWidth, BitVec.ofNat_add_ofNat, ← BitVec.ofNat_and,
    Nat.sub_add_cancel Nat.one_le_two_pow, Nat.and_comm (2 ^ w - 1),
    Nat.and_two_pow_sub_one_eq_mod]

/-- The mask constraint: the only fact about `m` surviving abstraction. -/
theorem mask_isMask {o w : Nat} {m : BitVec o} (hwo : w ≤ o)
    (hm : m = maskOfWidth o w) : m &&& (m + 1#o) = 0#o := by
  subst hm
  exact isMask_maskOfWidth hwo

/-- ANDing with `maskOfWidth o w` keeps exactly the low `w` bits. -/
theorem toNat_and_maskOfWidth {o w : Nat} (h : w ≤ o) (x : BitVec o) :
    (x &&& maskOfWidth o w).toNat = x.toNat % 2 ^ w := by
  rw [BitVec.toNat_and, toNat_maskOfWidth h, Nat.and_two_pow_sub_one_eq_mod]

/-- Introduction rule for every push lemma: it suffices that `b = a` mod `2^w`. -/
theorem setWidth_eq_and_maskOfWidth {w o : Nat} (h : w ≤ o) {a : BitVec w} {b : BitVec o}
    (hab : b.toNat % 2 ^ w = a.toNat) : a.setWidth o = b &&& maskOfWidth o w := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_and_maskOfWidth h, BitVec.toNat_setWidth_of_le h, hab]
