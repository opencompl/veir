module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Init.Data.Array.Basic

/-! CTree validity of the widening rules of `widenScalarPattern?`, at every target width.

`widenReverse .g_bswap` is only defined at the widths 16, 32 and 64, which the matcher cannot
require of the target width. -/

namespace Veir.Legalization.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base clearNswNuwProperties
  clearDisjointProperties

attribute [local implicit_reducible] TypeAttr


/-- A zero-extended shift amount converts to the same amount. -/
private theorem shiftAmount_zext {w W bw : Nat} (h : w < W) (a : Data.LLVM.Int w) :
    shiftAmount bw (a.zext W false h) = shiftAmount bw a := by
  have : a.getValueD.toNat % 2 ^ W = a.getValueD.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.getValueD.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h)))
  cases a <;> simp_all [shiftAmount, Data.LLVM.Int.zext, Id.run, BitVec.toNat_setWidth,
    Data.LLVM.Int.getValueD]


/-! ### Shifts

The amount of the wide shift is the amount of the narrow one when it is below the narrow width,
and the narrow shift is poison else. -/

/-- The shift amount, when it is below the width, as a bit-vector of that width. -/
private theorem shiftAmount_of_lt {v : Nat} (z : BitVec v) (hz : z.toNat < w) :
    shiftAmount w (Data.LLVM.Int.val z) = .val (BitVec.ofNat w z.toNat) := by
  simp [shiftAmount, hz]


/-- The shift amount, when it is at least the width, is all ones, so the shift is poison. -/
private theorem shiftAmount_of_le {v : Nat} (z : BitVec v) (hz : w ≤ z.toNat) :
    shiftAmount w (Data.LLVM.Int.val z) = .val (BitVec.allOnes w) := by
  simp [shiftAmount, Nat.not_lt.mpr hz]


/-- Dropping the no-wrap flags of `g_shl` can only remove poison. -/
private theorem shl_isRefinedBy_shl (x y : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.shl x y nsw nuw ⊒ Data.LLVM.Int.shl x y := by grind


/-- `widenTypeGroup .g_shl (.type 0) .g_anyext`: the any-extended operand shifted by the same amount,
without the no-wrap flags, truncated back. -/
private theorem shl_widening {v : Nat} (h : w < W) (x : Data.LLVM.Int w) (z : Data.LLVM.Int v) (m : BitVec (W - w))
    (nsw nuw : Bool) :
    Data.LLVM.Int.shl x (shiftAmount w z) nsw nuw ⊒
      Data.LLVM.Int.trunc (Data.LLVM.Int.shl (Data.LLVM.Int.ext x W m h) (shiftAmount W z)) w false false h := by
  cases x with
  | poison => simp [Data.LLVM.Int.shl, Data.LLVM.Int.ext, Id.run]
  | val x =>
  cases z with
  | poison => simp [shiftAmount, Data.LLVM.Int.shl, Id.run]
  | val z =>
  have hww : w < 2 ^ w := Nat.lt_two_pow_self
  have hWW : W < 2 ^ W := Nat.lt_two_pow_self
  by_cases hz : z.toNat < w
  · have hW : z.toNat < W := by omega
    rw [shiftAmount_of_lt z hz, shiftAmount_of_lt z hW]
    refine isRefinedBy_trans (shl_isRefinedBy_shl _ _ nsw nuw) ?_
    simp [Data.LLVM.Int.shl, Data.LLVM.Int.ext, Data.LLVM.Int.trunc, Data.LLVM.Int.cast, Id.run, BitVec.le_def,
      Nat.mod_eq_of_lt (Nat.lt_trans hz hww), Nat.mod_eq_of_lt (Nat.lt_trans hW hWW),
      Nat.mod_eq_of_lt hww, Nat.mod_eq_of_lt hWW, Nat.not_le.mpr hz, Nat.not_le.mpr hW,
      BitVec.setWidth_shiftLeft_of_le (Nat.le_of_lt h), BitVec.setWidth_append_eq_right]
  · rw [shiftAmount_of_le z (Nat.not_lt.mp hz)]
    have : BitVec.ofNat w w ≤ BitVec.allOnes w := by
      rw [BitVec.le_def]; simp [BitVec.toNat_ofNat, BitVec.toNat_allOnes]; omega
    simp [Data.LLVM.Int.shl, Id.run, pure, this]


/-- The width, as a bit-vector of that width, is at most all ones. -/
private theorem ofNat_width_le_allOnes : BitVec.ofNat w w ≤ BitVec.allOnes w := by
  have := Nat.lt_two_pow_self (n := w)
  rw [BitVec.le_def]; simp [BitVec.toNat_ofNat, BitVec.toNat_allOnes]; omega


/-- `widenTypeGroup .g_lshr (.type 0) .g_zext`: the zero-extended operand shifted by the same amount
truncated back; the `exact` check sees the same shifted-out bits. -/
private theorem lshr_widening {v : Nat} (h : w < W) (x : Data.LLVM.Int w) (z : Data.LLVM.Int v) (exact : Bool) :
    Data.LLVM.Int.lshr x (shiftAmount w z) exact ⊒
      Data.LLVM.Int.trunc (Data.LLVM.Int.lshr (Data.LLVM.Int.zext x W false h) (shiftAmount W z) exact)
        w false false h := by
  cases x with
  | poison => simp [Data.LLVM.Int.lshr, Data.LLVM.Int.zext, Id.run]
  | val x =>
  cases z with
  | poison => simp [shiftAmount, Data.LLVM.Int.lshr, Id.run]
  | val z =>
  have hww : w < 2 ^ w := Nat.lt_two_pow_self
  have hWW : W < 2 ^ W := Nat.lt_two_pow_self
  have hle := Nat.le_of_lt h
  by_cases hz : z.toNat < w
  · have hW : z.toNat < W := by omega
    rw [shiftAmount_of_lt z hz, shiftAmount_of_lt z hW]
    have hval : (x.setWidth W >>> z.toNat).setWidth w = x >>> z.toNat := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_setWidth_of_le hle]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)
    simp [Data.LLVM.Int.lshr, Data.LLVM.Int.zext, Data.LLVM.Int.trunc, Id.run, pure, BitVec.le_def,
      BitVec.ushiftRight_eq', Nat.mod_eq_of_lt (Nat.lt_trans hz hww), Nat.mod_eq_of_lt (Nat.lt_trans hW hWW),
      Nat.mod_eq_of_lt hww, Nat.mod_eq_of_lt hWW, Nat.not_le.mpr hz, Nat.not_le.mpr hW,
      Data.LLVM.ushiftRight_shiftLeft_eq_self_iff, BitVec.toNat_setWidth_of_le hle, hval]
    split <;> simp_all
  · rw [shiftAmount_of_le z (Nat.not_lt.mp hz)]
    simp [Data.LLVM.Int.lshr, Id.run, pure, ofNat_width_le_allOnes]


/-- `widenTypeGroup .g_ashr (.type 0) .g_sext`, as `lshr_widening`, through the signed values. -/
private theorem ashr_widening {v : Nat} (h : w < W) (x : Data.LLVM.Int w) (z : Data.LLVM.Int v) (exact : Bool) :
    Data.LLVM.Int.ashr x (shiftAmount w z) exact ⊒
      Data.LLVM.Int.trunc (Data.LLVM.Int.ashr (Data.LLVM.Int.sext x W h) (shiftAmount W z) exact)
        w false false h := by
  cases x with
  | poison => simp [Data.LLVM.Int.ashr, Data.LLVM.Int.sext, Id.run]
  | val x =>
  cases z with
  | poison => simp [shiftAmount, Data.LLVM.Int.ashr, Id.run]
  | val z =>
  have hww : w < 2 ^ w := Nat.lt_two_pow_self
  have hWW : W < 2 ^ W := Nat.lt_two_pow_self
  have hle := Nat.le_of_lt h
  by_cases hz : z.toNat < w
  · have hW : z.toNat < W := by omega
    rw [shiftAmount_of_lt z hz, shiftAmount_of_lt z hW]
    have hval : ((x.signExtend W).sshiftRight z.toNat).setWidth w = x.sshiftRight z.toNat := by
      apply BitVec.eq_of_toInt_eq
      rw [Data.LLVM.toInt_setWidth_of_le hle, BitVec.toInt_sshiftRight, BitVec.toInt_signExtend_of_le hle,
        ← BitVec.toInt_sshiftRight (x := x), Data.LLVM.bmod_toInt]
    simp [Data.LLVM.Int.ashr, Data.LLVM.Int.sext, Data.LLVM.Int.trunc, Id.run, pure, BitVec.le_def,
      BitVec.ushiftRight_eq', BitVec.sshiftRight_eq', Nat.mod_eq_of_lt (Nat.lt_trans hz hww),
      Nat.mod_eq_of_lt (Nat.lt_trans hW hWW), Nat.mod_eq_of_lt hww, Nat.mod_eq_of_lt hWW,
      Nat.not_le.mpr hz, Nat.not_le.mpr hW, Data.LLVM.ushiftRight_shiftLeft_eq_self_iff,
      Data.LLVM.toNat_signExtend_mod hle (Nat.le_of_lt hz), hval]
    split <;> simp_all
  · rw [shiftAmount_of_le z (Nat.not_lt.mp hz)]
    simp [Data.LLVM.Int.ashr, Id.run, pure, ofNat_width_le_allOnes]


/-- `widenReverse .g_bitreverse`: the reverse of the any-extended operand holds the reverse of the
operand in its high `w` bits, which the shift down by `W - w` moves to the low bits. The shift
amount is below `W` since `0 < w`, so it is not poison. -/
private theorem bitreverse_widening {w W : Nat} (hw : 0 < w) (h : w < W) (x : Data.LLVM.Int w) (m : BitVec (W - w)) :
    x.bitreverse ⊒
      ((x.ext W m h).bitreverse.lshr (shiftAmount W (.val (BitVec.ofInt W (↑W - ↑w))))).trunc w false false h := by
  cases x with
  | poison => simp [Data.LLVM.Int.bitreverse, Data.LLVM.Int.ext, Data.LLVM.Int.lshr, Id.run, pure]
  | val x =>
    have hd : (↑W - ↑w : _root_.Int) = ((W - w : Nat) : _root_.Int) := by omega
    have hlt : W - w < W := by omega
    have hlt2 : W - w < 2 ^ W := Nat.lt_trans hlt Nat.lt_two_pow_self
    have hWW : W < 2 ^ W := Nat.lt_two_pow_self
    rw [hd, BitVec.ofInt_natCast]
    simp only [shiftAmount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2, hlt, ite_true]
    simp [Data.LLVM.Int.bitreverse, Data.LLVM.Int.ext, Data.LLVM.Int.lshr, Data.LLVM.Int.trunc, Data.LLVM.Int.cast, Id.run,
      BitVec.le_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2, Nat.mod_eq_of_lt hWW,
      Nat.not_le.mpr hlt, BitVec.ushiftRight_eq', isRefinedBy_eq]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_setWidth, BitVec.getElem_reverse, BitVec.getMsbD_eq_getLsbD,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_reverse, BitVec.getMsbD_cast, BitVec.getLsbD_append]
    have e1 : W - 1 - (W - w + i) = w - 1 - i := by omega
    simp only [BitVec.getElem_cast, BitVec.getElem_reverse, BitVec.getMsbD_eq_getLsbD, BitVec.getLsbD_append,
      show W - w + w = W by omega, show W - w + i < W by omega, decide_true, Bool.true_and, e1,
      show w - 1 - i < w by omega, ite_true, BitVec.getLsbD_eq_getElem]
    simp [hi]

/-- A count resized to a wide type and truncated back is the count resized to the narrow type. -/
private theorem resizeCount_trunc {v w W : Nat} (h : W > w) (x : Data.LLVM.Int v) :
    (resizeCount W x).trunc w false false h = resizeCount w x := by
  cases x with
  | poison => simp [resizeCount, Data.LLVM.Int.trunc, Id.run]
  | val x =>
    have : (x.setWidth W).setWidth w = x.setWidth w := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_of_lt h))]
    simp [resizeCount, Data.LLVM.Int.trunc, Id.run, this]


/-- `widenCtlzSrc`: the leading zeros of the zero-extended operand, less the `W - w` added ones. -/
private theorem widen_ctlz_src {w W : Nat} (h : w < W) (a : Data.LLVM.Int w) :
    resizeCount W (a.ctlz false) ⊒
      (resizeCount W ((a.zext W false h).ctlz false)).sub (.val (BitVec.ofInt W (↑W - ↑w))) false true := by
  cases a with
  | poison => simp [resizeCount, Data.LLVM.Int.ctlz, Data.LLVM.Int.zext, Data.LLVM.Int.sub, Id.run]
  | val x =>
    have hc := Data.LLVM.toNat_clz_setWidth (Nat.le_of_lt h) x
    have hle : (BitVec.clz x).toNat ≤ w := by
      have := BitVec.clz_le (x := x)
      rw [BitVec.le_def] at this
      simpa [Nat.mod_eq_of_lt Nat.lt_two_pow_self] using this
    have hW : W < 2 ^ W := Nat.lt_two_pow_self
    have hd : (↑W - ↑w : _root_.Int) = ((W - w : Nat) : _root_.Int) := by omega
    simp only [resizeCount, Data.LLVM.Int.ctlz, Data.LLVM.Int.zext, Data.LLVM.Int.sub, Id.run,
      Bool.false_and, Bool.false_eq_true, false_and, ite_false, hd, BitVec.ofInt_natCast]
    simp only [BitVec.setWidth_eq, hc, BitVec.usubOverflow, BitVec.toNat_ofNat, decide_eq_true_eq,
      true_and]
    rw [Nat.mod_eq_of_lt (by omega : (BitVec.clz x).toNat + (W - w) < 2 ^ W),
      Nat.mod_eq_of_lt (by omega : W - w < 2 ^ W), ite_eq_right (by omega)]
    simp only [isRefinedBy_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : (BitVec.clz x).toNat + (W - w) < 2 ^ W),
      Nat.mod_eq_of_lt (by omega : W - w < 2 ^ W),
      show 2 ^ W - (W - w) + ((BitVec.clz x).toNat + (W - w)) = (BitVec.clz x).toNat + 2 ^ W by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- `widenCttzSrc`: the trailing zeros of the extended operand with bit `w` set. -/
private theorem widen_cttz_src {w W : Nat} (h : w < W) (a : Data.LLVM.Int w) (m : BitVec (W - w)) :
    resizeCount W (a.cttz false) ⊒
      resizeCount W (((a.ext W m h).or (.val (BitVec.ofInt W (2 ^ w)))).cttz true) := by
  cases a with
  | poison => simp [resizeCount, Data.LLVM.Int.cttz, Data.LLVM.Int.ext, Data.LLVM.Int.or, Id.run]
  | val x =>
    simp [resizeCount, Data.LLVM.Int.cttz, Data.LLVM.Int.ext, Data.LLVM.Int.or, Data.LLVM.Int.cast, Id.run,
      Data.LLVM.ext_or_two_pow_ne_zero h m x, isRefinedBy_eq, Data.LLVM.toNat_ctz_or_two_pow h m x]

/-- `widenScalar` of the operand of `g_ctpop` (type group 1) with `g_zext`: zero extension adds no
set bits. -/
private theorem widen_ctpop_src {w W v : Nat} (h : w < W) (a : Data.LLVM.Int w) :
    resizeCount v a.ctpop ⊒ resizeCount v (a.zext W false h).ctpop := by
  cases a with
  | poison => simp [resizeCount, Data.LLVM.Int.ctpop, Data.LLVM.Int.zext, Id.run]
  | val x =>
    have : (BitVec.cpop (x.setWidth W)).toNat = (BitVec.cpop x).toNat := by
      rw [BitVec.toNat_cpop, BitVec.toNat_cpop, BitVec.cpopNatRec_setWidth_of_le _ (Nat.le_refl _),
        show W = w + (W - w) by omega, BitVec.cpopNatRec_of_le _ _ (Nat.le_refl _)]
    simp [resizeCount, Data.LLVM.Int.ctpop, Data.LLVM.Int.zext, Id.run, isRefinedBy_eq, this]

theorem widen_icmp_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_icmp (.type 1) .g_sext W) := by
  proveLegalValid using Data.LLVM.icmp_sext

theorem widen_select_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_select (.type 1) .g_zext W) := by
  proveLegalValid using Data.LLVM.selectNonzero_zext

theorem widen_shl_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_shl (.type 1) .g_zext W) := by
  proveLegalValid using shiftAmount_zext

theorem widen_ashr_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ashr (.type 1) .g_zext W) := by
  proveLegalValid using shiftAmount_zext

theorem widen_lshr_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_lshr (.type 1) .g_zext W) := by
  proveLegalValid using shiftAmount_zext

theorem widen_ctlz_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ctlz (.type 0) .g_anyext W) := by
  proveLegalValid using resizeCount_trunc

theorem widen_cttz_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_cttz (.type 0) .g_anyext W) := by
  proveLegalValid using resizeCount_trunc

theorem widen_ctpop_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ctpop (.type 0) .g_anyext W) := by
  proveLegalValid using resizeCount_trunc

theorem widen_fshl_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_fshl (.type 1) .g_zext W) := by
  proveLegalValid using Data.LLVM.funnelShiftAmount_zext

theorem widen_fshr_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_fshr (.type 1) .g_zext W) := by
  proveLegalValid using Data.LLVM.funnelShiftAmount_zext

theorem widen_ctlz_1_valid (W : Nat) : Puddle.CTree.Pattern.Valid (widenCtlzSrc W) := by
  proveLegalValid using widen_ctlz_src

theorem widen_cttz_1_valid (W : Nat) : Puddle.CTree.Pattern.Valid (widenCttzSrc W) := by
  proveLegalValid using widen_cttz_src

theorem widen_ctpop_1_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ctpop (.type 1) .g_zext W) := by
  proveLegalValid using widen_ctpop_src

/-! ## The type-group rules

Each is closed by the local lemma of its operation in `Veir.Passes.Legalization.Proofs`. The
divisions also have undefined behavior at the wide width only when they have it at the narrow one,
which dismisses the goals where only the wide division is undefined. -/

theorem widen_add_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_add (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid using Data.LLVM.add_widening

theorem widen_sub_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_sub (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid using Data.LLVM.sub_widening

theorem widen_mul_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_mul (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid using Data.LLVM.mul_widening

theorem widen_and_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_and (.type 0) .g_anyext W) := by
  proveLegalValid using Data.LLVM.and_widening

theorem widen_or_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_or (.type 0) .g_anyext W clearDisjointProperties) := by
  proveLegalValid using Data.LLVM.or_widening

theorem widen_xor_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_xor (.type 0) .g_anyext W) := by
  proveLegalValid using Data.LLVM.xor_widening

theorem widen_select_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_select (.type 0) .g_anyext W) := by
  proveLegalValid using Data.LLVM.select_widen_values

theorem widen_shl_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_shl (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid using shl_widening

theorem widen_ashr_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ashr (.type 0) .g_sext W) := by
  proveLegalValid using ashr_widening

theorem widen_lshr_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_lshr (.type 0) .g_zext W) := by
  proveLegalValid using lshr_widening

theorem widen_sdiv_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_sdiv (.type 0) .g_sext W) := by
  proveLegalValid with first
    | (exfalso; have := Data.LLVM.isSignedDivisionUB_sext (by assumption) _ _ (by assumption); simp_all; done)
    | (apply Data.LLVM.sdiv_widening <;> simp_all; done)

theorem widen_srem_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_srem (.type 0) .g_sext W) := by
  proveLegalValid with first
    | (exfalso; have := Data.LLVM.isSignedDivisionUB_sext (by assumption) _ _ (by assumption); simp_all; done)
    | (apply Data.LLVM.srem_widening <;> simp_all; done)

theorem widen_udiv_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_udiv (.type 0) .g_zext W) := by
  proveLegalValid with first
    | (exfalso; simp_all [Data.LLVM.isUnsignedDivisionUB_zext]; done)
    | (apply Data.LLVM.udiv_widening <;> simp_all; done)

theorem widen_urem_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_urem (.type 0) .g_zext W) := by
  proveLegalValid with first
    | (exfalso; simp_all [Data.LLVM.isUnsignedDivisionUB_zext]; done)
    | (apply Data.LLVM.urem_widening <;> simp_all; done)

theorem widen_sext_inreg_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_sext_inreg (.type 0) .g_anyext W) := by
  proveLegalValid using Data.LLVM.sext_inreg_widening

theorem widen_smin_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_smin (.type 0) .g_sext W) := by
  proveLegalValid using Data.LLVM.smin_widening

theorem widen_smax_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_smax (.type 0) .g_sext W) := by
  proveLegalValid using Data.LLVM.smax_widening

theorem widen_umin_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_umin (.type 0) .g_sext W) := by
  proveLegalValid using Data.LLVM.umin_widening

theorem widen_umax_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_umax (.type 0) .g_sext W) := by
  proveLegalValid using Data.LLVM.umax_widening

theorem widen_abs_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_abs (.type 0) .g_sext W) := by
  proveLegalValid using Data.LLVM.abs_widening

theorem widen_uaddo_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_uaddo W) := by
  proveLegalValid using Data.LLVM.uaddo_widening

theorem widen_usubo_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_usubo W) := by
  proveLegalValid using Data.LLVM.usubo_widening

theorem widen_saddo_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_saddo W) := by
  proveLegalValid using Data.LLVM.saddo_widening

theorem widen_ssubo_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_ssubo W) := by
  proveLegalValid using Data.LLVM.ssubo_widening

/-- `widenConstant` creates the wide constant from the matched properties, which are split into
their value and type by hand, so that the value it is created with reduces. -/
theorem widen_constant_0_valid (W : Nat) : Puddle.CTree.Pattern.Valid (widenConstant W) := by
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  rename_i props _ _ _
  obtain ⟨⟨value, ⟨w, _⟩⟩⟩ := props
  simp [ctree_semantics, Attribute.of, -Attribute.integerType_eq_of] at *
  rw [ofInt_ofInt_value]
  exact Data.LLVM.trunc_ofInt_of_bmod_eq _ (by simpa using Data.LLVM.widenConstant_value_bmod w value)

/-- `widenTypeGroup .g_poison`: a wide poison truncates to poison, which any value refines. -/
theorem widen_poison_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_poison (.type 0) .g_anyext W) := by
  proveLegalValid with
    first
      | exact poison_isRefinedBy _
      | simp_all

/-- `widenTypeGroup .g_load`: a wider `g_load` reads the same `properties.size` bytes, and leaves
the high bits of its result unspecified as the narrow one does, so the source chooses the low
`w - size` of the high bits the target chose. The proof follows the interpreter's alignment check
and memory access step by step, which `simp` cannot traverse. -/
theorem widen_load_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_load (.type 0) .g_anyext W) := by
  conv => arg 1; cbv
  simpPuddleValid
  simpLegalSemantics
  normalizeLegalValid
  casesPointers
  -- The operand is poison or not an address: the source has undefined behavior or fails.
  all_goals try (simp [monadLift, MonadLift.monadLift, Bind.bind]; done)
  -- Distribute the lifted interpreter over its alignment check and load, and simulate them.
  all_goals simp only [monadLift_interp_bind, CTree.monadLift_interp_ok]
  all_goals simp only [Bind.bind, bind_bind, _root_.CTree.bind_pure]
  all_goals (refine Sim.bind (RR := Eq) _ _ _ _ (Sim.refl _ (fun _ => rfl) _) ?_; rintro _ _ rfl)
  all_goals (refine Sim.bind (RR := Eq) _ _ _ _ (Sim.refl _ (fun _ => rfl) _) ?_; rintro _ _ rfl)
  -- The source fails when its result is narrower than the load, and chooses its high bits else.
  all_goals simp_all [ctree_semantics, monadLift, MonadLift.monadLift, _root_.CTree.CTree.bind_tau,
    _root_.CTree.CTree.tau_def, Sim.tau_l, Sim.bind_monadLift_right_iff, Attribute.of,
    -Attribute.integerType_eq_of, le_eq_false_of_lt, lt_eq_false_of_le, RuntimeValue.isRefinedBy,
    Data.LLVM.trunc_zext, Data.LLVM.trunc_ext, Data.LLVM.trunc_ext_of_lt]
  all_goals (intro msb; exact ⟨_, by first | exact isRefinedBy_refl _ | rfl⟩)

theorem widen_bitreverse_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenReverse .g_bitreverse W) := by
  proveLegalValid using bitreverse_widening

/-- The result of a `g_icmp` is an `i1`, which the interpreter zero-extends to a wider result
type; the matcher excludes `i0`, so the narrow result is the `i1` or its zero extension. -/
theorem widen_icmp_0_valid (W : Nat) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_icmp (.type 0) .g_anyext W) := by
  proveLegalValid with first
    | simp_all [Data.LLVM.trunc_zext_of_lt]
    | (apply Data.LLVM.icmp_result_widening_one <;> omega)

/-! ## Status of every widening rule -/

@[legalization_status]
theorem widen_add_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_add (.type 0) .g_anyext W clearNswNuwProperties) :=
  .proven (widen_add_0_valid W)

@[legalization_status]
theorem widen_sub_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_sub (.type 0) .g_anyext W clearNswNuwProperties) :=
  .proven (widen_sub_0_valid W)

@[legalization_status]
theorem widen_icmp_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_icmp (.type 0) .g_anyext W) :=
  .proven (widen_icmp_0_valid W)

@[legalization_status]
theorem widen_icmp_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_icmp (.type 1) .g_sext W) :=
  .proven (widen_icmp_1_valid W)

@[legalization_status]
theorem widen_select_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_select (.type 0) .g_anyext W) :=
  .proven (widen_select_0_valid W)

@[legalization_status]
theorem widen_select_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_select (.type 1) .g_zext W) :=
  .proven (widen_select_1_valid W)

@[legalization_status]
theorem widen_shl_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_shl (.type 0) .g_anyext W clearNswNuwProperties) :=
  .proven (widen_shl_0_valid W)

@[legalization_status]
theorem widen_ashr_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ashr (.type 0) .g_sext W) :=
  .proven (widen_ashr_0_valid W)

@[legalization_status]
theorem widen_lshr_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_lshr (.type 0) .g_zext W) :=
  .proven (widen_lshr_0_valid W)

@[legalization_status]
theorem widen_shl_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_shl (.type 1) .g_zext W) :=
  .proven (widen_shl_1_valid W)

@[legalization_status]
theorem widen_ashr_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ashr (.type 1) .g_zext W) :=
  .proven (widen_ashr_1_valid W)

@[legalization_status]
theorem widen_lshr_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_lshr (.type 1) .g_zext W) :=
  .proven (widen_lshr_1_valid W)

@[legalization_status]
theorem widen_and_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_and (.type 0) .g_anyext W) :=
  .proven (widen_and_0_valid W)

@[legalization_status]
theorem widen_or_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_or (.type 0) .g_anyext W clearDisjointProperties) :=
  .proven (widen_or_0_valid W)

@[legalization_status]
theorem widen_xor_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_xor (.type 0) .g_anyext W) :=
  .proven (widen_xor_0_valid W)

@[legalization_status]
theorem widen_mul_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_mul (.type 0) .g_anyext W clearNswNuwProperties) :=
  .proven (widen_mul_0_valid W)

@[legalization_status]
theorem widen_sdiv_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_sdiv (.type 0) .g_sext W) :=
  .proven (widen_sdiv_0_valid W)

@[legalization_status]
theorem widen_srem_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_srem (.type 0) .g_sext W) :=
  .proven (widen_srem_0_valid W)

@[legalization_status]
theorem widen_udiv_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_udiv (.type 0) .g_zext W) :=
  .proven (widen_udiv_0_valid W)

@[legalization_status]
theorem widen_urem_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_urem (.type 0) .g_zext W) :=
  .proven (widen_urem_0_valid W)

@[legalization_status]
theorem widen_constant_0_status (W : Nat) :
    Status Unproven (widenConstant W) :=
  .proven (widen_constant_0_valid W)

@[legalization_status]
theorem widen_sext_inreg_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_sext_inreg (.type 0) .g_anyext W) :=
  .proven (widen_sext_inreg_0_valid W)

@[legalization_status]
theorem widen_ctlz_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ctlz (.type 0) .g_anyext W) :=
  .proven (widen_ctlz_0_valid W)

@[legalization_status]
theorem widen_cttz_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_cttz (.type 0) .g_anyext W) :=
  .proven (widen_cttz_0_valid W)

@[legalization_status]
theorem widen_ctpop_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ctpop (.type 0) .g_anyext W) :=
  .proven (widen_ctpop_0_valid W)

@[legalization_status]
theorem widen_ctlz_1_status (W : Nat) :
    Status Unproven (widenCtlzSrc W) :=
  .proven (widen_ctlz_1_valid W)

@[legalization_status]
theorem widen_cttz_1_status (W : Nat) :
    Status Unproven (widenCttzSrc W) :=
  .proven (widen_cttz_1_valid W)

@[legalization_status]
theorem widen_ctpop_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ctpop (.type 1) .g_zext W) :=
  .proven (widen_ctpop_1_valid W)

@[legalization_status]
theorem widen_poison_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_poison (.type 0) .g_anyext W) :=
  .proven (widen_poison_0_valid W)

@[legalization_status]
theorem widen_bswap_0_status (W : Nat) :
    Status Unproven (widenReverse .g_bswap W) :=
  .unproven .widthDependent

@[legalization_status]
theorem widen_bitreverse_0_status (W : Nat) :
    Status Unproven (widenReverse .g_bitreverse W) :=
  .proven (widen_bitreverse_0_valid W)

@[legalization_status]
theorem widen_smin_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_smin (.type 0) .g_sext W) :=
  .proven (widen_smin_0_valid W)

@[legalization_status]
theorem widen_smax_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_smax (.type 0) .g_sext W) :=
  .proven (widen_smax_0_valid W)

@[legalization_status]
theorem widen_umin_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_umin (.type 0) .g_sext W) :=
  .proven (widen_umin_0_valid W)

@[legalization_status]
theorem widen_umax_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_umax (.type 0) .g_sext W) :=
  .proven (widen_umax_0_valid W)

@[legalization_status]
theorem widen_abs_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_abs (.type 0) .g_sext W) :=
  .proven (widen_abs_0_valid W)

@[legalization_status]
theorem widen_fshl_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_fshl (.type 1) .g_zext W) :=
  .proven (widen_fshl_1_valid W)

@[legalization_status]
theorem widen_fshr_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_fshr (.type 1) .g_zext W) :=
  .proven (widen_fshr_1_valid W)

@[legalization_status]
theorem widen_uaddo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_uaddo W) :=
  .proven (widen_uaddo_0_valid W)

@[legalization_status]
theorem widen_usubo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_usubo W) :=
  .proven (widen_usubo_0_valid W)

@[legalization_status]
theorem widen_saddo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_saddo W) :=
  .proven (widen_saddo_0_valid W)

@[legalization_status]
theorem widen_ssubo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_ssubo W) :=
  .proven (widen_ssubo_0_valid W)

@[legalization_status]
theorem widen_load_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_load (.type 0) .g_anyext W) :=
  .proven (widen_load_0_valid W)

end Veir.Legalization.CTreeProofs
