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

`widenReverse .g_bitreverse` shifts the reversed wide operand down by `W - w`, which is the whole
wide width for a source width `w = 0`, so the shift is poison there. `widenConstant` reads the
value of the constant at the width of its attribute, which the matcher does not tie to the width
of its result. -/

namespace Veir.Legalization.CTreeProofs

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr


/-- A zero-extended shift amount converts to the same amount. -/
private theorem shiftAmount_zext {w W bw : Nat} (h : w < W) (a : Data.LLVM.Int w) :
    shiftAmount bw (a.zext W false h) = shiftAmount bw a := by
  have : a.getValueD.toNat % 2 ^ W = a.getValueD.toNat :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le a.getValueD.isLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h)))
  cases a <;> simp_all [shiftAmount, Data.LLVM.Int.zext, Id.run, BitVec.toNat_setWidth,
    Data.LLVM.Int.getValueD]


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

/-! ## Status of every widening rule -/

@[legalization_status]
theorem widen_add_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_add (.type 0) .g_anyext W clearNswNuwProperties) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_sub_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_sub (.type 0) .g_anyext W clearNswNuwProperties) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_icmp_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_icmp (.type 0) .g_anyext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_icmp_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_icmp (.type 1) .g_sext W) :=
  .proven (widen_icmp_1_valid W)

@[legalization_status]
theorem widen_select_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_select (.type 0) .g_anyext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_select_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_select (.type 1) .g_zext W) :=
  .proven (widen_select_1_valid W)

@[legalization_status]
theorem widen_shl_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_shl (.type 0) .g_anyext W clearNswNuwProperties) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_ashr_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ashr (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_lshr_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_lshr (.type 0) .g_zext W) :=
  .unproven .needsTypedMatch

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
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_or_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_or (.type 0) .g_anyext W clearDisjointProperties) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_xor_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_xor (.type 0) .g_anyext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_mul_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_mul (.type 0) .g_anyext W clearNswNuwProperties) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_sdiv_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_sdiv (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_srem_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_srem (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_udiv_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_udiv (.type 0) .g_zext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_urem_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_urem (.type 0) .g_zext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_constant_0_status (W : Nat) :
    Status Unproven (widenConstant W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_sext_inreg_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_sext_inreg (.type 0) .g_anyext W) :=
  .unproven .needsTypedMatch

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
theorem widen_bswap_0_status (W : Nat) :
    Status Unproven (widenReverse .g_bswap W) :=
  .unproven .widthDependent

@[legalization_status]
theorem widen_bitreverse_0_status (W : Nat) :
    Status Unproven (widenReverse .g_bitreverse W) :=
  .unproven .widthDependent

@[legalization_status]
theorem widen_smin_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_smin (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_smax_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_smax (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_umin_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_umin (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_umax_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_umax (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_abs_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_abs (.type 0) .g_sext W) :=
  .unproven .needsTypedMatch

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
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_usubo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_usubo W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_saddo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_saddo W) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem widen_ssubo_0_status (W : Nat) :
    Status Unproven (widenScalarAddSubOverflow .g_ssubo W) :=
  .unproven .needsTypedMatch

/-- A wider `g_load` reads the same `properties.size` bytes and leaves the high bits of its result
unspecified, as `g_anyext` does. -/
@[legalization_status]
theorem widen_load_0_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_load (.type 0) .g_anyext W) :=
  .unproven .notYetProven

end Veir.Legalization.CTreeProofs
