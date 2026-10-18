module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Data.LLVM.Int.Basic
import Init.Tactics

namespace Veir.Passes.InstCombineLLVM

open Veir Veir.Data

public theorem bitvec_shift_mul_constant {w : Nat} (x c1 c2 : BitVec w) :
    (x <<< c2) * c1 = x * (c1 <<< c2) := by
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq',
    BitVec.shiftLeft_eq_mul_twoPow, BitVec.shiftLeft_eq_mul_twoPow]
  ac_rfl

public theorem mul_shift_constant_refines (w : Nat) (x : LLVM.Int w)
    (c1 c2 : BitVec w) (hin : c2.toNat < w) :
    LLVM.Int.mul (LLVM.Int.shl x (.val c2)) (.val c1) ⊒
      LLVM.Int.mul x (.val (c1 <<< c2)) := by
  cases x with
  | poison => simp [LLVM.Int.mul, LLVM.Int.shl, Id.run]
  | val x =>
    simp only [LLVM.Int.mul, LLVM.Int.shl, Id.run, Bool.false_eq_true, false_and,
      ↓reduceIte]
    have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
    have hcoerce : (w : BitVec w).toNat = w := by
      change w % 2 ^ w = w
      exact Nat.mod_eq_of_lt hwlt
    simp only [BitVec.le_def, hcoerce]
    rw [if_neg (Nat.not_le_of_lt hin)]
    rw [isRefinedBy_eq]
    exact bitvec_shift_mul_constant x c1 c2

public theorem mul_shift_constant_drop_flags_refines (w : Nat) (x : LLVM.Int w)
    (c1 c2 : BitVec w) (hin : c2.toNat < w)
    (shiftNSW shiftNUW mulNSW mulNUW : Bool) :
    LLVM.Int.mul (LLVM.Int.shl x (.val c2) shiftNSW shiftNUW) (.val c1)
        mulNSW mulNUW ⊒
      LLVM.Int.mul x (.val (c1 <<< c2)) false false := by
  cases x with
  | poison => simp [LLVM.Int.mul, LLVM.Int.shl, Id.run]
  | val x =>
    have hwlt : w < 2 ^ w := Nat.lt_two_pow_self
    have hcoerce : (w : BitVec w).toNat = w := by
      change w % 2 ^ w = w
      exact Nat.mod_eq_of_lt hwlt
    simp only [LLVM.Int.shl, Id.run, BitVec.le_def, hcoerce]
    rw [if_neg (Nat.not_le_of_lt hin)]
    by_cases hsnw : shiftNSW = true ∧ (x <<< c2).sshiftRight' c2 ≠ x
    · rw [if_pos hsnw]
      simp [LLVM.Int.mul, isRefinedBy_eq, Id.run]
    by_cases hnuw : shiftNUW = true ∧ (x <<< c2) >>> c2 ≠ x
    · rw [if_neg hsnw, if_pos hnuw]
      simp [LLVM.Int.mul, isRefinedBy_eq, Id.run]
    rw [if_neg hsnw, if_neg hnuw]
    simp only [LLVM.Int.mul, Id.run]
    by_cases hmnw : mulNSW = true ∧ (x <<< c2).smulOverflow c1 = true
    · rw [if_pos hmnw]
      simp [isRefinedBy_eq, pure]
    by_cases hmuw : mulNUW = true ∧ (x <<< c2).umulOverflow c1 = true
    · rw [if_neg hmnw, if_pos hmuw]
      simp [isRefinedBy_eq, pure]
    rw [if_neg hmnw, if_neg hmuw, isRefinedBy_eq]
    exact bitvec_shift_mul_constant x c1 c2

/-- Reassociating a left shift through multiplication preserves unsigned
    no-wrap when both source operations carry `nuw`. -/
public theorem bitvec_mul_shift_nuw {w : Nat} (x c1 c2 : BitVec w)
    (hshift : (x <<< c2) >>> c2 = x)
    (hmul : BitVec.umulOverflow (x <<< c2) c1 = false) :
    BitVec.umulOverflow x (c1 <<< c2) = false := by
  simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_false_iff_not,
    Nat.not_le] at hmul ⊢
  have hs := congrArg BitVec.toNat hshift
  simp only [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq] at hs
  rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  let n := c2.toNat
  let p := 2 ^ n
  let m := 2 ^ w
  have hs' : (x.toNat * p % m) / p = x.toNat := by
    simpa [n, p, m, Nat.shiftRight_eq_div_pow] using hs
  have hrem : x.toNat * p % m < m := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hxpm : x.toNat * p < m := by
    calc
      x.toNat * p = (x.toNat * p % m) / p * p := by rw [hs']
      _ ≤ x.toNat * p % m := Nat.div_mul_le_self _ _
      _ < m := hrem
  have hshiftNat : (x <<< c2).toNat = x.toNat * p := by
    rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt hxpm]
  rw [hshiftNat] at hmul
  have hmodle : c1.toNat * p % m ≤ c1.toNat * p := Nat.mod_le _ _
  calc
    x.toNat * (c1.toNat * p % m) ≤ x.toNat * (c1.toNat * p) :=
      Nat.mul_le_mul_left _ hmodle
    _ = (x.toNat * p) * c1.toNat := by ac_rfl
    _ < m := hmul

public theorem mul_shift_constant_nuw_refines (w : Nat) (x : LLVM.Int w)
    (c1 c2 : BitVec w) (hin : c2.toNat < w)
    (shiftNSW mulNSW : Bool) :
    LLVM.Int.mul (LLVM.Int.shl x (.val c2) shiftNSW true) (.val c1)
        mulNSW true ⊒
      LLVM.Int.mul x (.val (c1 <<< c2)) false true := by
  cases x with
  | poison => simp [LLVM.Int.mul, LLVM.Int.shl, Id.run]
  | val x =>
    rw [LLVM.Int.isRefinedBy_iff]
    constructor
    · intro hs
      simp only [LLVM.Int.isPoison_mul, LLVM.Int.isPoison_shl,
        LLVM.Int.isPoison_of_val, false_or, ite_false,
        LLVM.Int.getValue_of_val, Bool.false_and, Bool.true_and] at hs ⊢
      simp at hs ⊢
      rcases hs with ⟨hshiftDefined, _, hmul⟩
      simp only [LLVM.Int.getValue_shl] at hmul
      simp only [LLVM.Int.getValue_of_val] at hmul
      apply bitvec_mul_shift_nuw x c1 c2
      · exact hshiftDefined.2.1
      · exact hmul
    · intro hs ht
      rw [LLVM.Int.getValue_mul _ _ hs, LLVM.Int.getValue_mul _ _ ht,
        LLVM.Int.getValue_shl]
      simp only [LLVM.Int.getValue_of_val]
      exact bitvec_shift_mul_constant x c1 c2

private theorem shift_toInt_eq_of_signed_exact {w : Nat} (x c2 : BitVec w)
    (hin : c2.toNat < w) (hshift : (x <<< c2).sshiftRight' c2 = x) :
    (x <<< c2).toInt = x.toInt * (2 ^ c2.toNat : Nat) := by
  have hs := congrArg BitVec.toInt hshift
  simp only [BitVec.toInt_sshiftRight'] at hs
  rw [Int.shiftRight_eq_div_pow] at hs
  let n := c2.toNat
  let p : Int := (2 ^ n : Nat)
  let q : Int := (x.toNat : Int) * p
  let m : Nat := 2 ^ w
  have hnle : n ≤ w := Nat.le_of_lt hin
  have hpMNat : 2 ^ n ∣ 2 ^ w := Nat.pow_dvd_pow 2 hnle
  have hpM : p ∣ (m : Int) := by
    change ((2 ^ n : Nat) : Int) ∣ ((2 ^ w : Nat) : Int)
    rcases hpMNat with ⟨k, hk⟩
    refine ⟨(k : Int), ?_⟩
    simpa only [← Int.natCast_mul] using
      congrArg (fun z : Nat => (z : Int)) hk
  have hpq : p ∣ q := by
    exact ⟨x.toNat, by simp [q, Int.mul_comm]⟩
  have hpdiff : p ∣ q.bmod m - q :=
    Int.dvd_trans hpM (Int.dvd_bmod_sub_self (x := q) (m := m))
  have hpmod : p ∣ q.bmod m := by
    have h := Int.dvd_add hpq hpdiff
    rw [← Int.add_sub_assoc, Int.add_comm q, Int.add_sub_cancel] at h
    exact h
  have hsrepr : (x <<< c2).toInt = q.bmod m := by
    simp [q, m, n, p, BitVec.toInt_shiftLeft, Nat.shiftLeft_eq]
  have hsdiv : (x <<< c2).toInt / p = x.toInt := by
    simpa [p, n] using hs
  calc
    (x <<< c2).toInt = (x <<< c2).toInt / p * p := by
      rw [hsrepr, Int.ediv_mul_cancel hpmod]
    _ = x.toInt * p := by rw [hsdiv]
    _ = x.toInt * (2 ^ c2.toNat : Nat) := by rfl

private theorem ofInt_twoPow_eq {w n : Nat} (h : n < w) :
    BitVec.ofInt w ((2 ^ n : Nat) : Int) = BitVec.twoPow w n := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_of_lt (by decide) h),
    BitVec.toNat_twoPow_of_lt h]

private theorem shifted_eq_ofInt_signed_product {w : Nat} (c1 c2 : BitVec w)
    (hin : c2.toNat < w) :
    c1 <<< c2 = BitVec.ofInt w (c1.toInt * (2 ^ c2.toNat : Nat)) := by
  let n := c2.toNat
  let p : Int := (2 ^ n : Nat)
  have hpow : BitVec.twoPow w n = BitVec.ofInt w p := by
    exact (ofInt_twoPow_eq hin).symm
  calc
    c1 <<< c2 = c1 * BitVec.twoPow w n := by
      rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow]
    _ = BitVec.ofInt w c1.toInt * BitVec.ofInt w p := by
      rw [BitVec.ofInt_toInt, hpow]
    _ = BitVec.ofInt w (c1.toInt * p) := (BitVec.ofInt_mul _ _).symm

/-- Reassociating a left shift through multiplication preserves signed
    no-wrap when both source operations carry `nsw` and the folded constant is
    not signed minimum. -/
public theorem bitvec_mul_shift_nsw {w : Nat} (x c1 c2 : BitVec w)
    (hin : c2.toNat < w) (hshift : (x <<< c2).sshiftRight' c2 = x)
    (hmul : BitVec.smulOverflow (x <<< c2) c1 = false)
    (hnotmin : c1 <<< c2 ≠ BitVec.intMin w) :
    BitVec.smulOverflow x (c1 <<< c2) = false := by
  have hw : 0 < w := Nat.zero_lt_of_lt hin
  let r : Int := (2 ^ (w - 1) : Nat)
  let p : Int := (2 ^ c2.toNat : Nat)
  let a : Int := x.toInt
  let b : Int := c1.toInt
  let q : Int := b * p
  have hrpos : 0 < r := by
    change 0 < ((2 ^ (w - 1) : Nat) : Int)
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hp : 0 < p := by
    change 0 < ((2 ^ c2.toNat : Nat) : Int)
    exact Int.natCast_pos.mpr (Nat.two_pow_pos _)
  have hshiftInt : (x <<< c2).toInt = a * p := by
    simpa [a, p] using shift_toInt_eq_of_signed_exact x c2 hin hshift
  simp only [BitVec.smulOverflow, Bool.or_eq_false_iff,
    decide_eq_false_iff_not, Int.not_le, Int.not_lt] at hmul ⊢
  rw [hshiftInt] at hmul
  change a * p * b < r ∧ -r ≤ a * p * b at hmul
  have hsource : a * q < r ∧ -r ≤ a * q := by
    simpa [q, Int.mul_assoc, Int.mul_comm p b] using hmul
  by_cases ha0 : a = 0
  · have hx0 : x.toInt = 0 := by simpa [a] using ha0
    simp only [hx0, Int.zero_mul]
    change 0 < r ∧ -r ≤ 0
    exact ⟨hrpos, Int.neg_nonpos_of_nonneg (Int.le_of_lt hrpos)⟩
  have haqBounds : -r ≤ q ∧ q ≤ r := by
    rcases Int.lt_trichotomy a 0 with haNeg | haZero | haPos
    · have hale : a ≤ -1 := by omega
      constructor
      · by_cases hn : -r ≤ q
        · exact hn
        · have hqle : q < -r := Int.lt_of_not_ge hn
          have hqnonpos : q ≤ 0 := by omega
          have hprod : (-1 : Int) * q ≤ a * q :=
            Int.mul_le_mul_of_nonpos_right hale hqnonpos
          omega
      · by_cases hn : q ≤ r
        · exact hn
        · have hrq : r < q := Int.lt_of_not_ge hn
          have hqnonneg : 0 ≤ q := by omega
          have hprod : a * q ≤ (-1 : Int) * q :=
            Int.mul_le_mul_of_nonneg_right hale hqnonneg
          omega
    · exact (ha0 haZero).elim
    · have haone : 1 ≤ a := by omega
      constructor
      · by_cases hn : -r ≤ q
        · exact hn
        · have hqle : q < -r := Int.lt_of_not_ge hn
          have hqnonpos : q ≤ 0 := by omega
          have hprod : a * q ≤ (1 : Int) * q :=
            Int.mul_le_mul_of_nonpos_right haone hqnonpos
          omega
      · by_cases hn : q ≤ r
        · exact hn
        · have hrq : r < q := Int.lt_of_not_ge hn
          have hqnonneg : 0 ≤ q := by omega
          have hprod : (1 : Int) * q ≤ a * q :=
            Int.mul_le_mul_of_nonneg_right haone hqnonneg
          omega
  have hqUpper : q < r := by
    rcases Int.lt_or_eq_of_le haqBounds.2 with hlt | heq
    · exact hlt
    · exfalso
      apply hnotmin
      rw [shifted_eq_ofInt_signed_product c1 c2 hin]
      change BitVec.ofInt w q = BitVec.intMin w
      rw [heq]
      change BitVec.ofInt w ((2 ^ (w - 1) : Nat) : Int) = BitVec.intMin w
      rw [ofInt_twoPow_eq (by omega)]
      rfl
  have hfoldedInt : (c1 <<< c2).toInt = q := by
    rw [shifted_eq_ofInt_signed_product c1 c2 hin]
    exact BitVec.toInt_ofInt_eq_self hw haqBounds.1 hqUpper
  rw [hfoldedInt]
  simpa [a, r] using hsource

public theorem mul_shift_constant_nsw_refines (w : Nat) (x : LLVM.Int w)
    (c1 c2 : BitVec w) (hin : c2.toNat < w) (hnotmin : c1 <<< c2 ≠ BitVec.intMin w)
    (shiftNUW mulNUW : Bool) :
    LLVM.Int.mul (LLVM.Int.shl x (.val c2) true shiftNUW) (.val c1)
        true mulNUW ⊒
      LLVM.Int.mul x (.val (c1 <<< c2)) true false := by
  cases x with
  | poison => simp [LLVM.Int.mul, LLVM.Int.shl, Id.run]
  | val x =>
    rw [LLVM.Int.isRefinedBy_iff]
    constructor
    · intro hs
      simp only [LLVM.Int.isPoison_mul, LLVM.Int.isPoison_shl,
        LLVM.Int.isPoison_of_val, false_or, ite_false,
        LLVM.Int.getValue_of_val, Bool.true_and] at hs ⊢
      simp at hs ⊢
      rcases hs with ⟨hshiftDefined, hmul, _⟩
      simp only [LLVM.Int.getValue_shl, LLVM.Int.getValue_of_val] at hmul
      apply bitvec_mul_shift_nsw x c1 c2 hin
      · exact hshiftDefined.1
      · exact hmul
      · exact hnotmin
    · intro hs ht
      rw [LLVM.Int.getValue_mul _ _ hs, LLVM.Int.getValue_mul _ _ ht,
        LLVM.Int.getValue_shl]
      simp only [LLVM.Int.getValue_of_val]
      exact bitvec_shift_mul_constant x c1 c2

end Veir.Passes.InstCombineLLVM
