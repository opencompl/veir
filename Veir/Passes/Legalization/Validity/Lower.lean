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
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide

/-! CTree validity of the lowerings of `lower?` and the narrowings of `narrowScalar?`.

`lowerSext` passes the source width as a 64-bit `g_sext_inreg` size, so it is wrong from width
`2^64`; `lowerFunnelShift` shifts the other operand by one, which is poison at width 1, and computes
the amount in the amount's type, which the matcher does not require to hold the width. The
narrowings match the width `2 * W`, which the interpreter of `g_merge_values` produces as `W + W`,
so their local lemmas are stated up to that cast. -/

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

/-- A count whose zero input is poison refines the count that is defined at zero. -/
private theorem ctlz_zero_poison {v w : Nat} (x : Data.LLVM.Int v) :
    resizeCount w (x.ctlz true) ⊒ resizeCount w (x.ctlz false) := by
  cases x with
  | poison => simp [resizeCount, Data.LLVM.Int.ctlz, Id.run]
  | val x => by_cases h : x = 0#v <;> simp [resizeCount, Data.LLVM.Int.ctlz, Id.run, h, isRefinedBy_eq, pure]

private theorem cttz_zero_poison {v w : Nat} (x : Data.LLVM.Int v) :
    resizeCount w (x.cttz true) ⊒ resizeCount w (x.cttz false) := by
  cases x with
  | poison => simp [resizeCount, Data.LLVM.Int.cttz, Id.run]
  | val x => by_cases h : x = 0#v <;> simp [resizeCount, Data.LLVM.Int.cttz, Id.run, h, isRefinedBy_eq, pure]

/-- Copied from `Veir.Passes.Legalization.Proofs`, where it is private. -/
private theorem uadde_lowering {w : Nat} (h : 1 < w) (x y : Data.LLVM.Int w) (c : Data.LLVM.Int 1) :
    uaddWithCarry x y c =
      let tmp := Data.LLVM.Int.add x y
      let carry := Data.LLVM.Int.icmp tmp x Data.LLVM.IntPred.ult
      let sum := Data.LLVM.Int.add tmp (Data.LLVM.Int.zext c w false h)
      let carry2 := Data.LLVM.Int.and (Data.LLVM.Int.icmp sum (Data.LLVM.Int.constant w 0) Data.LLVM.IntPred.eq) c
      (sum, Data.LLVM.Int.or carry carry2) := by
  cases x <;> cases y <;> cases c
  case val.val.val x y c =>
    obtain ⟨b, rfl⟩ := c.exists_eq_ofBool
    -- It carries if either `g_add` carries.
    simp [uaddWithCarry, Data.LLVM.Int.add, Data.LLVM.Int.icmp, Data.LLVM.Int.zext, Data.LLVM.Int.and, Data.LLVM.Int.or,
      Data.LLVM.Int.constant, Id.run, Data.LLVM.IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.carry_eq_uaddOverflow_or (by omega : 0 < w), BitVec.uaddOverflow_eq_ult_left x y,
      BitVec.uaddOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- The other seven cases have a poison operand, so both sides reduce to poison.
  all_goals rfl

/-- Copied from `Veir.Passes.Legalization.Proofs`, where it is private. -/
private theorem usube_lowering {w : Nat} (h : 1 < w) (x y : Data.LLVM.Int w) (b : Data.LLVM.Int 1) :
    usubWithBorrow x y b =
      let tmp := Data.LLVM.Int.sub x y
      let borrow := Data.LLVM.Int.icmp tmp x Data.LLVM.IntPred.ugt
      let diff := Data.LLVM.Int.sub tmp (Data.LLVM.Int.zext b w false h)
      let borrow2 := Data.LLVM.Int.and (Data.LLVM.Int.icmp tmp (Data.LLVM.Int.constant w 0) Data.LLVM.IntPred.eq) b
      (diff, Data.LLVM.Int.or borrow borrow2) := by
  cases x <;> cases y <;> cases b
  case val.val.val x y b =>
    obtain ⟨b, rfl⟩ := b.exists_eq_ofBool
    -- It borrows if either `g_sub` borrows.
    simp [usubWithBorrow, Data.LLVM.Int.sub, Data.LLVM.Int.icmp, Data.LLVM.Int.zext, Data.LLVM.Int.and, Data.LLVM.Int.or,
      Data.LLVM.Int.constant, Id.run, Data.LLVM.IntPred.eval, BitVec.ofBool_or_ofBool, BitVec.ofBool_and_ofBool,
      BitVec.ult_setWidth_add_ofBool (by omega : 0 < w), BitVec.usubOverflow_eq_ult_sub x y,
      BitVec.usubOverflow_setWidth_ofBool (by omega : 0 < w)]
  -- The other seven cases have a poison operand, so both sides reduce to poison.
  all_goals rfl

/-- The zero constant of an integer attribute. -/
private theorem IntegerAttr.ofInt_zero_value (t : IntegerType) : (IntegerAttr.ofInt 0 t).value = 0 := by
  simp [IntegerAttr.ofInt, IntegerAttr.normalizeValue]

/-- `lowerShlSat true`: `sshl.sat a b = a != (a << b) >>s b ? (a <s 0 ? INT_MIN : INT_MAX) : a << b`. -/
private theorem sshlSat_lowering {w v : Nat} (x : Data.LLVM.Int w) (a : Data.LLVM.Int v) :
    x.sshlSat (shiftAmount w a) ⊒
      GMIR.selectNonzero (x.icmp ((x.shl (shiftAmount w a)).ashr (shiftAmount w a)) .ne)
        (GMIR.selectNonzero (x.icmp (.val 0#w) .slt) (.val (BitVec.ofInt w (-2 ^ (w - 1))))
          (.val (BitVec.ofInt w (2 ^ (w - 1) - 1))))
        (x.shl (shiftAmount w a)) := by
  cases x <;> cases a <;> simp [shiftAmount, Data.LLVM.Int.sshlSat, Data.LLVM.Int.shl, Data.LLVM.Int.ashr,
    Data.LLVM.Int.icmp, GMIR.selectNonzero, Id.run, isRefinedBy_eq, pure, Data.LLVM.IntPred.eval]
  rename_i x a
  generalize (if a.toNat < w then BitVec.setWidth w a else BitVec.allOnes w) = s
  -- An amount of at least the width makes the source poison.
  by_cases hpo : BitVec.ofNat w w ≤ s
  · simp only [ite_eq_left hpo]
  simp only [ite_eq_right hpo]
  by_cases hov : (x <<< s.toNat).sshiftRight s.toNat = x
  · simp [hov]
  · have : (x != (x <<< s.toNat).sshiftRight s.toNat) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact fun h => hov h.symm
    simp only [hov, this, not_false_eq_true, ite_true, BitVec.ofBool_true, BitVec.slt_zero_eq_msb]
    cases x.msb <;> simp [BitVec.intMin_eq_neg_two_pow, Data.LLVM.intMax_eq_ofInt]

/-- `lowerShlSat false`: `ushl.sat a b = a != (a << b) >>u b ? UINT_MAX : a << b`. -/
private theorem ushlSat_lowering {w v : Nat} (x : Data.LLVM.Int w) (a : Data.LLVM.Int v) :
    x.ushlSat (shiftAmount w a) ⊒
      GMIR.selectNonzero (x.icmp ((x.shl (shiftAmount w a)).lshr (shiftAmount w a)) .ne)
        (.val (BitVec.ofInt w (-1))) (x.shl (shiftAmount w a)) := by
  cases x <;> cases a <;> simp [shiftAmount, Data.LLVM.Int.ushlSat, Data.LLVM.Int.shl, Data.LLVM.Int.lshr,
    Data.LLVM.Int.icmp, GMIR.selectNonzero, Id.run, isRefinedBy_eq, pure, Data.LLVM.IntPred.eval]
  rename_i x a
  generalize (if a.toNat < w then BitVec.setWidth w a else BitVec.allOnes w) = s
  by_cases hpo : BitVec.ofNat w w ≤ s
  · simp only [ite_eq_left hpo]
  simp only [ite_eq_right hpo]
  by_cases hov : x <<< s.toNat >>> s.toNat = x
  · simp [hov]
  · have : (x != x <<< s.toNat >>> s.toNat) = true := by
      simp only [bne_iff_ne, ne_eq]
      exact fun h => hov h.symm
    simp [hov, this, Data.LLVM.ofInt_neg_one]

theorem lower_zext_valid : Puddle.CTree.Pattern.Valid lowerZext := by
  proveLegalValid using Data.LLVM.zext_and_anyext

/-- `lowerSext`: the high bits a `g_anyext` chooses are overwritten by the `g_sext_inreg` of the
source width, so the result is the sign extension of the source whatever it chose. -/
theorem sext_anyext_inreg {w W : Nat} (h : w < W) (x : Data.LLVM.Int w) (msb : BitVec (W - w)) :
    x.sext W h ⊒ ((x.ext W msb h).trunc w false false h).sext W h := by
  sorry

/-- The matcher bounds the source width by `2 ^ 64`, so the `sz` of the `g_sext_inreg` reads back
as the source width. -/
-- theorem lower_sext_valid : Puddle.CTree.Pattern.Valid lowerSext := by
--   proveLegalValid with
--   (
--     expose_names
--     simp [FreezeC] at x
--     veir_bv_normalize
--     simp
--     intro
--     ext k hk
--     simp [BitVec.getElem_signExtend, -BitVec.toNat_ofNat]
--     split
--     · split
--       · simp [BitVec.getLsbD_append, show k < bitwidth by omega]
--       · simp [BitVec.msb_setWidth, -BitVec.toNat_ofNat ]
--         by_cases hlt : 0 < (BitVec.ofNat 64 bitwidth).toNat
--         · simp [hlt, -BitVec.toNat_ofNat, BitVec.getLsbD_append]
--           split
--           · simp [← BitVec.getLsbD_eq_getElem, -BitVec.toNat_ofNat,]
--             congr
--             simp at *
--             sorry
--           ·
--             sorry
--         · simp [show bitwidth % 18446744073709551616 = 0 by omega]
--           sorry
--     · sorry
--     )

theorem lower_uaddsat_valid : Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_uaddsat false true) := by
  proveLegalValid using Data.LLVM.uaddSat_minmax

theorem lower_usubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_usubsat false false) := by
  proveLegalValid using Data.LLVM.usubSat_minmax

theorem lower_saddsat_valid : Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_saddsat true true) := by
  proveLegalValid using Data.LLVM.saddSat_minmax

theorem lower_ssubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_ssubsat true false) := by
  proveLegalValid using Data.LLVM.ssubSat_minmax

theorem lower_sshlsat_valid : Puddle.CTree.Pattern.Valid (lowerShlSat true) := by
  proveLegalValid using sshlSat_lowering

theorem lower_ushlsat_valid : Puddle.CTree.Pattern.Valid (lowerShlSat false) := by
  proveLegalValid using ushlSat_lowering

theorem lower_ctlz_zero_poison_valid :
    Puddle.CTree.Pattern.Valid (lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz) := by
  proveLegalValid using ctlz_zero_poison

theorem lower_cttz_zero_poison_valid :
    Puddle.CTree.Pattern.Valid (lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz) := by
  proveLegalValid using cttz_zero_poison

theorem lower_uadde_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE true) := by
  proveLegalValid with simp_all [uadde_lowering, Data.LLVM.Int.constant, IntegerAttr.ofInt_zero_value]

theorem lower_usube_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE false) := by
  proveLegalValid with simp_all [usube_lowering, Data.LLVM.Int.constant, IntegerAttr.ofInt_zero_value]

/-- Copied from `Veir.Passes.Legalization.Proofs`, where it is private. -/
private theorem add_isRefinedBy_add {w : Nat} (x y : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.add x y nsw nuw ⊒ Data.LLVM.Int.add x y := by
  grind

/-- Copied from `Veir.Passes.Legalization.Proofs`, where it is private. -/
private theorem sub_isRefinedBy_sub {w : Nat} (x y : Data.LLVM.Int w) (nsw nuw : Bool) :
    Data.LLVM.Int.sub x y nsw nuw ⊒ Data.LLVM.Int.sub x y := by
  grind

/-- `narrowAddSub true`, at the width `n = k + k` of the matched operands, where `k` is the half
width the interpreter of `g_unmerge_values` computes, and up to the casts of the interpreters of
`g_unmerge_values` and `g_merge_values`: the sum of the low halves, and the sum with carry of the
high halves, as `add_narrowing` of `Veir.Passes.Legalization.Proofs`. The validity goal
existentially quantifies a width equation `P` its body does not use. -/
private theorem add_narrowing_cast {n k : Nat} (h : n = k + k) (x y : Data.LLVM.Int n)
    (nsw nuw : Bool) {P : Prop} (hP : P) :
    ∃ _ : P, (x.add y nsw nuw).cast h ⊒
      mergeValues ((unmergeValues (x.cast h)).1.add (unmergeValues (y.cast h)).1)
        (uaddWithCarry (unmergeValues (x.cast h)).2 (unmergeValues (y.cast h)).2
          ((unmergeValues (x.cast h)).1.uaddOverflowFlag (unmergeValues (y.cast h)).1)).1 := by
  subst h
  refine ⟨hP, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (add_isRefinedBy_add x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [Data.LLVM.Int.add, Data.LLVM.Int.uaddOverflowFlag, unmergeValues, uaddWithCarry, mergeValues,
      Id.run, BitVec.add_eq_append]
  all_goals exact poison_isRefinedBy _

/-- `narrowAddSub false`, as `add_narrowing_cast`. -/
private theorem sub_narrowing_cast {n k : Nat} (h : n = k + k) (x y : Data.LLVM.Int n)
    (nsw nuw : Bool) {P : Prop} (hP : P) :
    ∃ _ : P, (x.sub y nsw nuw).cast h ⊒
      mergeValues ((unmergeValues (x.cast h)).1.sub (unmergeValues (y.cast h)).1)
        (usubWithBorrow (unmergeValues (x.cast h)).2 (unmergeValues (y.cast h)).2
          ((unmergeValues (x.cast h)).1.usubOverflowFlag (unmergeValues (y.cast h)).1)).1 := by
  subst h
  refine ⟨hP, ?_⟩
  simp only [Data.LLVM.Int.cast_self]
  refine isRefinedBy_trans (sub_isRefinedBy_sub x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [Data.LLVM.Int.sub, Data.LLVM.Int.usubOverflowFlag, unmergeValues, usubWithBorrow, mergeValues,
      Id.run, BitVec.sub_eq_append]
  all_goals exact poison_isRefinedBy _

theorem lower_uaddo_valid : Puddle.CTree.Pattern.Valid (lowerUAddSubO true) := by
  proveLegalValid using Data.LLVM.uaddo_flag_lowering

theorem lower_usubo_valid : Puddle.CTree.Pattern.Valid (lowerUAddSubO false) := by
  proveLegalValid using Data.LLVM.usubo_flag_lowering

theorem lower_saddo_valid : Puddle.CTree.Pattern.Valid (lowerSAddSubO true) := by
  proveLegalValid using Data.LLVM.saddo_lowering

theorem lower_ssubo_valid : Puddle.CTree.Pattern.Valid (lowerSAddSubO false) := by
  proveLegalValid using Data.LLVM.ssubo_lowering

/-- The matcher fixes the width `2 * W`, which the interpreter halves to `2 * W / 2`; the width
equations are arithmetic. -/
theorem narrow_add_valid (W : Nat) : Puddle.CTree.Pattern.Valid (narrowAddSub true W) := by
  proveLegalValid with (apply add_narrowing_cast <;> omega)

theorem narrow_sub_valid (W : Nat) : Puddle.CTree.Pattern.Valid (narrowAddSub false W) := by
  proveLegalValid with (apply sub_narrowing_cast <;> omega)

/-! ## Status of every lowering and narrowing -/

@[legalization_status]
theorem lower_sext_status :
    Status Unproven (lowerSext) :=
  .proven lower_sext_valid

@[legalization_status]
theorem lower_zext_status :
    Status Unproven (lowerZext) :=
  .proven lower_zext_valid

@[legalization_status]
theorem lower_fshl_status :
    Status Unproven (lowerFunnelShift true) :=
  .unproven .widthDependent

@[legalization_status]
theorem lower_fshr_status :
    Status Unproven (lowerFunnelShift false) :=
  .unproven .widthDependent

@[legalization_status]
theorem lower_ctlz_zero_poison_status :
    Status Unproven (lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz) :=
  .proven lower_ctlz_zero_poison_valid

@[legalization_status]
theorem lower_cttz_zero_poison_status :
    Status Unproven (lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz) :=
  .proven lower_cttz_zero_poison_valid

@[legalization_status]
theorem lower_uaddsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_uaddsat false true) :=
  .proven lower_uaddsat_valid

@[legalization_status]
theorem lower_usubsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_usubsat false false) :=
  .proven lower_usubsat_valid

@[legalization_status]
theorem lower_saddsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_saddsat true true) :=
  .proven lower_saddsat_valid

@[legalization_status]
theorem lower_ssubsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_ssubsat true false) :=
  .proven lower_ssubsat_valid

@[legalization_status]
theorem lower_sshlsat_status :
    Status Unproven (lowerShlSat true) :=
  .proven lower_sshlsat_valid

@[legalization_status]
theorem lower_ushlsat_status :
    Status Unproven (lowerShlSat false) :=
  .proven lower_ushlsat_valid

@[legalization_status]
theorem lower_uaddo_status :
    Status Unproven (lowerUAddSubO true) :=
  .proven lower_uaddo_valid

@[legalization_status]
theorem lower_usubo_status :
    Status Unproven (lowerUAddSubO false) :=
  .proven lower_usubo_valid

@[legalization_status]
theorem lower_saddo_status :
    Status Unproven (lowerSAddSubO true) :=
  .proven lower_saddo_valid

@[legalization_status]
theorem lower_ssubo_status :
    Status Unproven (lowerSAddSubO false) :=
  .proven lower_ssubo_valid

@[legalization_status]
theorem lower_uadde_status :
    Status Unproven (lowerAddSubE true) :=
  .proven lower_uadde_valid

@[legalization_status]
theorem lower_usube_status :
    Status Unproven (lowerAddSubE false) :=
  .proven lower_usube_valid

@[legalization_status]
theorem narrow_add_status (W : Nat) :
    Status Unproven (narrowAddSub true W) :=
  .proven (narrow_add_valid W)

@[legalization_status]
theorem narrow_sub_status (W : Nat) :
    Status Unproven (narrowAddSub false W) :=
  .proven (narrow_sub_valid W)

end Veir.Legalization.CTreeProofs
