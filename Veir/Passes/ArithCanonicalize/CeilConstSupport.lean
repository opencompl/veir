import Veir.Passes.ArithCanonicalize.DivisionSupport

namespace Veir.ArithCanonicalize

open Veir Veir.Data
private theorem nat_ceil (n b : Nat) :
    (if n = 0 then 0 else (n - 1) / b + 1) =
      (if n % b = 0 then n / b else n / b + 1) := by
  cases n with
  | zero => simp
  | succ m =>
    have hd : (m + 1) / b = m / b + if (m + 1) % b = 0 then 1 else 0 := by
      simpa [Nat.dvd_iff_mod_eq_zero] using (Nat.succ_div (a := m) (b := b))
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
    by_cases hr : (m + 1) % b = 0
    · simp [hr] at hd ⊢
      omega
    · simp [hr] at hd ⊢
      omega

private theorem bitvec_ceil (w : Nat) (a b : BitVec w) (hb : b ≠ 0#w) :
    uceilResult (.val a) (.val b) =
      .val (if a % b = 0#w then a / b else a / b + 1#w) := by
  have hw : 0 < w := by
    by_cases h : 0 < w
    · exact h
    · have hz : w = 0 := by omega
      subst w
      exact False.elim (hb BitVec.of_length_zero)
  have hb0 : b.toNat ≠ 0 := by
    intro h
    apply hb
    exact BitVec.eq_of_toNat_eq (by simpa using h)
  by_cases ha : a = 0#w
  · simp [uceilResult, ha, LLVM.Int.select, LLVM.Int.icmp,
      LLVM.IntPred.eval, Id.run]
  · have ha0 : a.toNat ≠ 0 := by
      intro h
      apply ha
      exact BitVec.eq_of_toNat_eq (by simpa using h)
    have hle : (1#w : BitVec w) ≤ a := by
      simp [BitVec.le_def, BitVec.toNat_one hw]
      omega
    have hsub : (a - 1#w).toNat = a.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_one hw]
    have hbeq : (a == 0#w) = false := by simpa [beq_iff_eq] using ha
    simp [uceilResult, LLVM.Int.select, LLVM.Int.icmp,
      LLVM.IntPred.eval, LLVM.Int.sub, LLVM.Int.udiv,
      LLVM.Int.add, Id.run, hbeq, hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_one hw, BitVec.toNat_udiv,
      hsub]
    have hrEq : (a % b = 0#w) ↔ (a.toNat % b.toNat = 0) := by
      constructor
      · intro h
        have := congrArg BitVec.toNat h
        simpa [BitVec.toNat_umod] using this
      · intro h
        apply BitVec.eq_of_toNat_eq
        simpa [BitVec.toNat_umod] using h
    have hc := nat_ceil a.toNat b.toNat
    simp only [ha0, ↓reduceIte] at hc
    by_cases hr : a % b = 0#w
    · have hrNat := hrEq.mp hr
      simp [hrNat] at hc
      have hquotlt : a.toNat / b.toNat < 2 ^ w := by
        simpa [BitVec.toNat_udiv] using (BitVec.isLt (a / b))
      simp [hr, hc, Nat.mod_eq_of_lt hquotlt]
    · have hrNat := mt hrEq.mpr hr
      simp [hrNat] at hc
      simp [hr, hc]


theorem uceil_const_refines (w : Nat) (a b : BitVec w) (hb : b ≠ 0#w) :
    RuntimeValue.int w (uceilResult (.val a) (.val b)) ⊒
      .int w (.val (if a % b = 0#w then a / b else a / b + 1#w)) := by
  rw [bitvec_ceil w a b hb]
  simp [RuntimeValue.isRefinedBy, isRefinedBy]

end Veir.ArithCanonicalize
