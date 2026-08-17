module
/-! # Masks as bitvector variables constrained by `m &&& (m + 1) = 0`. -/

namespace Veir.Data.PBV

public section

/-- `maskOfWidth o w : BitVec o` has its low `w` bits set and all higher bits clear. -/
def maskOfWidth (o w : Nat) : BitVec o := BitVec.ofNat o (2 ^ w - 1)

/-- `m.IsMask` holds when `m = 2^k - 1` for some `k`; the only fact the bitblaster gets about a
width. -/
def IsMask {o : Nat} (m : BitVec o) : Prop := m &&& (m + 1#o) = 0#o

theorem ofNat_setWidth : BitVec.ofNat w x = BitVec.setWidth w (BitVec.ofNat w x)
  :=
  by grind


theorem isMask_maskOfWidth {o w : Nat} (_h : w <= o)
  : IsMask (maskOfWidth o w) :=
  by
  unfold IsMask
  unfold maskOfWidth
  rw[BitVec.ofNat_add_ofNat]
  rw[← BitVec.ofNat_and]
  rw[Nat.sub_add_cancel]
  apply BitVec.eq_of_getLsbD_eq
  intro i hio
  rw[@BitVec.getLsbD_zero o i]
  rw[BitVec.getLsbD_ofNat]
  rw[decide_eq_true hio]
  rw[Bool.true_and, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  rw[Bool.and_eq_false_imp, decide_eq_true_eq]
  intro h_iw
  grind
  grind

/-- The mask constraint, stated for a named mask: the only fact about `m` surviving abstraction. -/
theorem mask_isMask {o w : Nat} {m : BitVec o} (hwo : w ≤ o)
    (hm : m = maskOfWidth o w) : m &&& (m + 1#o) = 0#o := by
  subst hm
  exact isMask_maskOfWidth hwo
