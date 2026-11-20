module

import all Veir.Passes.Legalization.Validity.Common
import Veir.Passes.Legalization.Proofs
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.ProofKind

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
  | val x => by_cases h : x = 0#v <;> simp [resizeCount, Data.LLVM.Int.ctlz, Id.run, h, Data.LLVM.Int.isRefinedBy_eq, pure]

private theorem cttz_zero_poison {v w : Nat} (x : Data.LLVM.Int v) :
    resizeCount w (x.cttz true) ⊒ resizeCount w (x.cttz false) := by
  cases x with
  | poison => simp [resizeCount, Data.LLVM.Int.cttz, Id.run]
  | val x => by_cases h : x = 0#v <;> simp [resizeCount, Data.LLVM.Int.cttz, Id.run, h, Data.LLVM.Int.isRefinedBy_eq, pure]

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
    Data.LLVM.Int.icmp, GMIR.selectNonzero, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure, Data.LLVM.IntPred.eval]
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
    cases x.msb <;> simp [BitVec.intMin_eq_neg_two_pow, BitVec.intMax_eq_ofInt]

/-- `lowerShlSat false`: `ushl.sat a b = a != (a << b) >>u b ? UINT_MAX : a << b`. -/
private theorem ushlSat_lowering {w v : Nat} (x : Data.LLVM.Int w) (a : Data.LLVM.Int v) :
    x.ushlSat (shiftAmount w a) ⊒
      GMIR.selectNonzero (x.icmp ((x.shl (shiftAmount w a)).lshr (shiftAmount w a)) .ne)
        (.val (BitVec.ofInt w (-1))) (x.shl (shiftAmount w a)) := by
  cases x <;> cases a <;> simp [shiftAmount, Data.LLVM.Int.ushlSat, Data.LLVM.Int.shl, Data.LLVM.Int.lshr,
    Data.LLVM.Int.icmp, GMIR.selectNonzero, Id.run, Data.LLVM.Int.isRefinedBy_eq, pure, Data.LLVM.IntPred.eval]
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

@[proof_manual]
theorem lower_sext_valid : Puddle.CTree.Pattern.Valid lowerSext := by
  proveLegalValid with
  (
    expose_names
    simp only [FreezeC] at x
    veir_bv_normalize
    simp only [BitVec.setWidth_cast, forall_const, true_and]
    intro
    ext k hk
    simp only [BitVec.getElem_signExtend, BitVec.toNat_ofNat, Nat.reducePow,
      BitVec.getElem_setWidth, dite_eq_ite]
    rw [Nat.mod_eq_of_lt (by exact h)] at *
    split
    · simp only [BitVec.getLsbD_append]
      split
      · simp [BitVec.getLsbD_append, show k < bitwidth by omega]
      · simp [← BitVec.getLsbD_eq_getElem]
    · simp only [BitVec.msb_setWidth, BitVec.toNat_ofNat, Nat.reducePow]
      rw [Nat.mod_eq_of_lt (by exact h)] at *
      by_cases hzero : bitwidth = 0
      · subst hzero
        simp [BitVec.msb]
      · simp [show 0 < bitwidth by omega, BitVec.getLsbD_append, BitVec.msb,
          show bitwidth - 1 < bitwidth by omega, BitVec.getMsbD_eq_getLsbD, ← BitVec.getLsbD_eq_getElem]
    )

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

@[proof_manual]
theorem lower_uadde_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE true) := by
  proveLegalValid with simp_all [uadde_lowering, Data.LLVM.Int.constant, IntegerAttr.ofInt_zero_value]

@[proof_manual]
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
  refine Data.LLVM.Int.isRefinedBy_trans (add_isRefinedBy_add x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [Data.LLVM.Int.add, Data.LLVM.Int.uaddOverflowFlag, unmergeValues, uaddWithCarry, mergeValues,
      Id.run, BitVec.add_eq_append]
  all_goals exact Data.LLVM.Int.poison_isRefinedBy _

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
  refine Data.LLVM.Int.isRefinedBy_trans (sub_isRefinedBy_sub x y nsw nuw) ?_
  cases x <;> cases y
  case val.val x y =>
    simp [Data.LLVM.Int.sub, Data.LLVM.Int.usubOverflowFlag, unmergeValues, usubWithBorrow, mergeValues,
      Id.run, BitVec.sub_eq_append]
  all_goals exact Data.LLVM.Int.poison_isRefinedBy _

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
theorem lower_fshl_status :
    Status Unproven (lowerFunnelShift true) :=
  .unproven .widthDependent

@[legalization_status]
theorem lower_fshr_status :
    Status Unproven (lowerFunnelShift false) :=
  .unproven .widthDependent

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


/-! ## Three-way comparisons and multiply-high -/

/-- Zero-extending a set flag gives one. -/
private theorem setWidth_one (w : Nat) : (1#1).setWidth w = 1#w := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- Zero-extending a clear flag gives zero. -/
private theorem setWidth_zero_one (w : Nat) : (0#1).setWidth w = 0#w := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- The signed three-way comparison is the difference of the zero-extended `sgt` and `slt` flags. -/
private theorem scmp_bits {w₁ w₂ : Nat} (a b : BitVec w₁) :
    (if a.slt b then -1#w₂ else if a = b then 0#w₂ else 1#w₂) =
      (BitVec.ofBool (b.slt a)).setWidth w₂ - (BitVec.ofBool (a.slt b)).setWidth w₂ := by
  rcases Int.lt_trichotomy a.toInt b.toInt with hlt | heq | hgt
  · simp [BitVec.slt, hlt, Int.not_lt.mpr (Int.le_of_lt hlt), setWidth_one, setWidth_zero_one, BitVec.zero_sub]
  · obtain rfl : a = b := BitVec.toInt_inj.mp heq
    simp [BitVec.slt]
  · have hne : a ≠ b := by rintro rfl; exact Int.lt_irrefl _ hgt
    simp [BitVec.slt, hgt, Int.not_lt.mpr (Int.le_of_lt hgt), hne, setWidth_one, setWidth_zero_one]

/-- The unsigned three-way comparison is the difference of the zero-extended `ugt` and `ult` flags. -/
private theorem ucmp_bits {w₁ w₂ : Nat} (a b : BitVec w₁) :
    (if a.ult b then -1#w₂ else if a = b then 0#w₂ else 1#w₂) =
      (BitVec.ofBool (b.ult a)).setWidth w₂ - (BitVec.ofBool (a.ult b)).setWidth w₂ := by
  rcases Nat.lt_trichotomy a.toNat b.toNat with hlt | heq | hgt
  · simp [BitVec.ult, hlt, Nat.not_lt.mpr (Nat.le_of_lt hlt), setWidth_one, setWidth_zero_one, BitVec.zero_sub]
  · obtain rfl : a = b := BitVec.toNat_inj.mp heq
    simp [BitVec.ult]
  · have hne : a ≠ b := by rintro rfl; exact Nat.lt_irrefl _ hgt
    simp [BitVec.ult, hgt, Nat.not_lt.mpr (Nat.le_of_lt hgt), hne, setWidth_one, setWidth_zero_one]

/-- `lowerThreewayCompare true`. -/
private theorem scmp_lowering {w₁ w₂ : Nat} (h : 1 < w₂) (x y : Data.LLVM.Int w₁) :
    x.scmp y w₂ ⊒ ((x.icmp y .sgt).zext w₂ false h).sub ((x.icmp y .slt).zext w₂ false h) := by
  cases x <;> cases y <;>
    simp [Data.LLVM.Int.scmp, Data.LLVM.Int.icmp, Data.LLVM.Int.zext, Data.LLVM.Int.sub, Id.run,
      pure, Data.LLVM.IntPred.eval, scmp_bits]

/-- `lowerThreewayCompare false`. -/
private theorem ucmp_lowering {w₁ w₂ : Nat} (h : 1 < w₂) (x y : Data.LLVM.Int w₁) :
    x.ucmp y w₂ ⊒ ((x.icmp y .ugt).zext w₂ false h).sub ((x.icmp y .ult).zext w₂ false h) := by
  cases x <;> cases y <;>
    simp [Data.LLVM.Int.ucmp, Data.LLVM.Int.icmp, Data.LLVM.Int.zext, Data.LLVM.Int.sub, Id.run,
      pure, Data.LLVM.IntPred.eval, ucmp_bits]

@[proof_manual]
theorem lower_scmp_valid : Puddle.CTree.Pattern.Valid (lowerThreewayCompare true) := by
  proveLegalValid using scmp_lowering

@[proof_manual]
theorem lower_ucmp_valid : Puddle.CTree.Pattern.Valid (lowerThreewayCompare false) := by
  proveLegalValid using ucmp_lowering

/-- The high half of a double-width product is the product shifted down by the width. -/
private theorem extractLsb'_eq_setWidth_sshiftRight (w : Nat) (p : BitVec (w + w)) :
    p.extractLsb' w w = (p.sshiftRight w).setWidth w := by
  ext i hi
  simp [BitVec.getLsbD_sshiftRight, show w + i < w + w by omega]
  intros; omega

private theorem extractLsb'_eq_setWidth_ushiftRight (w : Nat) (p : BitVec (w + w)) :
    p.extractLsb' w w = (p.ushiftRight w).setWidth w := by
  ext i hi
  simp [BitVec.getLsbD_ushiftRight, hi]

/-- `lowerMulh true`: the double width `2 * w` is `w + w`, at which `smulHigh` is defined. -/
private theorem smulh_lowering {w w₂ : Nat} (hw : w₂ = w + w) (hpos : 0 < w) (x y : Data.LLVM.Int w) :
    x.smulHigh y ⊒
      (((x.sext w₂ (by omega)).mul (y.sext w₂ (by omega))).ashr
        (shiftAmount w₂ (Data.LLVM.Int.val (BitVec.ofNat w₂ w)))).trunc w false false (by omega) := by
  subst hw
  have hlt2 : w + w < 2 ^ (w + w) := by
    first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow_self _
  have hlt : w < 2 ^ (w + w) := by omega
  cases x <;> cases y <;>
    simp [Data.LLVM.Int.smulHigh, Data.LLVM.Int.sext, Data.LLVM.Int.mul, Data.LLVM.Int.ashr,
      Data.LLVM.Int.trunc, shiftAmount, Id.run, pure, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hlt2, BitVec.le_def, BitVec.sshiftRight', hpos,
      show ¬ w + w ≤ w by omega, extractLsb'_eq_setWidth_sshiftRight]

/-- `lowerMulh false`. -/
private theorem umulh_lowering {w w₂ : Nat} (hw : w₂ = w + w) (hpos : 0 < w) (x y : Data.LLVM.Int w) :
    x.umulHigh y ⊒
      (((x.zext w₂ false (by omega)).mul (y.zext w₂ false (by omega))).lshr
        (shiftAmount w₂ (Data.LLVM.Int.val (BitVec.ofNat w₂ w)))).trunc w false false (by omega) := by
  subst hw
  have hlt2 : w + w < 2 ^ (w + w) := by
    first | exact Nat.lt_two_pow_self | exact Nat.lt_two_pow_self _
  have hlt : w < 2 ^ (w + w) := by omega
  cases x <;> cases y <;>
    simp [Data.LLVM.Int.umulHigh, Data.LLVM.Int.zext, Data.LLVM.Int.mul, Data.LLVM.Int.lshr,
      Data.LLVM.Int.trunc, shiftAmount, Id.run, pure, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      Nat.mod_eq_of_lt hlt2, BitVec.le_def, BitVec.ushiftRight_eq', hpos,
      show ¬ w + w ≤ w by omega, extractLsb'_eq_setWidth_ushiftRight]

@[proof_manual]
theorem lower_smulh_valid : Puddle.CTree.Pattern.Valid (lowerMulh true) := by
  proveLegalValid with
    first
      | (simp_all; done)
      | (refine smulh_lowering ?_ ?_ _ _ <;> omega)

@[proof_manual]
theorem lower_umulh_valid : Puddle.CTree.Pattern.Valid (lowerMulh false) := by
  proveLegalValid with
    first
      | (simp_all; done)
      | (refine umulh_lowering ?_ ?_ _ _ <;> omega)

@[legalization_status]
theorem lower_scmp_status : Status Unproven (lowerThreewayCompare true) :=
  .proven lower_scmp_valid

@[legalization_status]
theorem lower_ucmp_status : Status Unproven (lowerThreewayCompare false) :=
  .proven lower_ucmp_valid

@[legalization_status]
theorem lower_smulh_status : Status Unproven (lowerMulh true) :=
  .proven lower_smulh_valid

@[legalization_status]
theorem lower_umulh_status : Status Unproven (lowerMulh false) :=
  .proven lower_umulh_valid

end Veir.Legalization.CTreeProofs
