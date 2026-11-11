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

/-! CTree validity of the widening rules of `widenScalarPattern?`, at every target width. -/

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

attribute [local implicit_reducible] TypeAttr Veir._propertiesOf GMIR.propertiesOf


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
  .unproven .notYetProven

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
  .unproven .notYetProven

@[legalization_status]
theorem widen_cttz_1_status (W : Nat) :
    Status Unproven (widenCttzSrc W) :=
  .unproven .notYetProven

@[legalization_status]
theorem widen_ctpop_1_status (W : Nat) :
    Status Unproven (widenTypeGroup .g_ctpop (.type 1) .g_zext W) :=
  .unproven .notYetProven

@[legalization_status]
theorem widen_bswap_0_status (W : Nat) :
    Status Unproven (widenReverse .g_bswap W) :=
  .unproven .widthDependent

@[legalization_status]
theorem widen_bitreverse_0_status (W : Nat) :
    Status Unproven (widenReverse .g_bitreverse W) :=
  .unproven .notYetProven

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

end Veir.Legalization.CTreeProofs
