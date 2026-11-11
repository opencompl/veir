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

/-! CTree validity of the RISC-V custom legalizations of `riscv64LegalizerInfo.legalizeCustom`. The
word rules work at the concrete widths 32 and 64, so their local lemmas are decided. -/

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

theorem custom_add_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_addw) := by
  proveLegalValid using Data.LLVM.add_drop_flags

theorem custom_sub_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_subw) := by
  proveLegalValid using Data.LLVM.sub_drop_flags

theorem custom_mul_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_mulw) := by
  proveLegalValid using Data.LLVM.mul_drop_flags

private theorem shl_word (x y : Data.LLVM.Int 32) (nsw nuw : Bool) :
    x.shl (shiftAmount 32 y) nsw nuw ⊒ x.shl (shiftAmount 32 (GMIR_RISCV.wordShiftAmount y)) := by
  have h31 : ∀ y : BitVec 32, y.toNat &&& 31 < 32 :=
    fun _ => Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases y with y | _
  · by_cases h : y.toNat < 32
    · have hlt : y < 32#32 := by bv_omega
      have hy : y &&& 31#32 = y := by bv_decide
      simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run, h, hy,
        BitVec.toNat_and, h31, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      veir_bv_decide
    · simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run, h,
        BitVec.toNat_and, h31, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      veir_bv_decide
  · simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run]
    veir_bv_decide

private theorem lshr_word (x y : Data.LLVM.Int 32) (exact : Bool) :
    x.lshr (shiftAmount 32 y) exact ⊒ x.lshr (shiftAmount 32 (GMIR_RISCV.wordShiftAmount y)) := by
  have h31 : ∀ y : BitVec 32, y.toNat &&& 31 < 32 :=
    fun _ => Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases y with y | _
  · by_cases h : y.toNat < 32
    · have hlt : y < 32#32 := by bv_omega
      have hy : y &&& 31#32 = y := by bv_decide
      simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run, h, hy,
        BitVec.toNat_and, h31, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      veir_bv_decide
    · simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run, h,
        BitVec.toNat_and, h31, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      veir_bv_decide
  · simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run]
    veir_bv_decide

private theorem ashr_word (x y : Data.LLVM.Int 32) (exact : Bool) :
    x.ashr (shiftAmount 32 y) exact ⊒ x.ashr (shiftAmount 32 (GMIR_RISCV.wordShiftAmount y)) := by
  have h31 : ∀ y : BitVec 32, y.toNat &&& 31 < 32 :=
    fun _ => Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  rcases y with y | _
  · by_cases h : y.toNat < 32
    · have hlt : y < 32#32 := by bv_omega
      have hy : y &&& 31#32 = y := by bv_decide
      simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run, h, hy,
        BitVec.toNat_and, h31, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      veir_bv_decide
    · simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run, h,
        BitVec.toNat_and, h31, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      veir_bv_decide
  · simp only [shiftAmount, GMIR_RISCV.wordShiftAmount, Data.LLVM.Int.and, Id.run]
    veir_bv_decide

theorem custom_shl_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_sllw) := by
  proveLegalValid using shl_word

theorem custom_lshr_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_srlw) := by
  proveLegalValid using lshr_word

theorem custom_ashr_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_sraw) := by
  proveLegalValid using ashr_word

theorem custom_sdiv_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_divw) := by
  proveLegalValid using Data.LLVM.sdiv_drop_exact

theorem custom_udiv_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_divuw) := by
  proveLegalValid using Data.LLVM.udiv_drop_exact

theorem custom_urem_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_remuw) := by
  proveLegalValid using isRefinedBy_refl

theorem custom_ctlz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_clzw) := by
  proveLegalValid using isRefinedBy_refl

theorem custom_cttz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_ctzw) := by
  proveLegalValid using isRefinedBy_refl

/-- `customLegalizeAbs`: the absolute value of an `i64` is the larger of it and its negation. -/
private theorem abs_smax_neg (x : Data.LLVM.Int 64) :
    x.abs false ⊒ x.smax ((Data.LLVM.Int.val 0#64).sub x) := by
  veir_bv_decide

theorem custom_abs_valid : Puddle.CTree.Pattern.Valid customLegalizeAbs := by
  proveLegalValid using abs_smax_neg

/-- `customLegalizeBitreverse8`: the low byte of `brev8` of an any-extended `i8` is its bit
reverse. -/
private theorem bitreverse_brev8 (x : Data.LLVM.Int 8) (m : BitVec 56) (h : 8 < 64) (h' : 64 > 8) :
    x.bitreverse ⊒ (brev8 (x.ext 64 m h)).trunc 8 false false h' := by
  rcases x with x | _
  · simp only [brev8, Data.LLVM.Int.ext, Data.LLVM.Int.bswap, Data.LLVM.Int.bitreverse,
      Data.LLVM.Int.trunc, Data.LLVM.Int.cast, Data.LLVM.Int.bswap64BV, Id.run, reduceIte,
      Nat.reduceEqDiff, dite_false, dite_true]
    simp only [isRefinedBy_eq]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp only [BitVec.getElem_reverse, BitVec.getElem_setWidth, BitVec.getLsbD_reverse,
      BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, BitVec.getElem_cast]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [BitVec.getMsbD, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb, BitVec.getLsbD_cast] <;>
      bv_decide
  · simp [Data.LLVM.Int.bitreverse, Id.run, isRefinedBy_eq]

theorem custom_bitreverse_valid : Puddle.CTree.Pattern.Valid customLegalizeBitreverse8 := by
  proveLegalValid using bitreverse_brev8

/-- The amount `w - 1` of the `g_ashr` that extracts the sign of a `w`-bit value. -/
private theorem shiftAmount_width_sub_one {w : Nat} (hw : 0 < w) :
    shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w (↑w - 1))) = .val (BitVec.ofNat w (w - 1)) := by
  have hlt : w - 1 < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le w 1) Nat.lt_two_pow_self
  rw [show (↑w - 1 : _root_.Int) = ((w - 1 : Nat) : _root_.Int) by omega, BitVec.ofInt_natCast]
  simp [shiftAmount, Nat.mod_eq_of_lt hlt, show w - 1 < w by omega]

/-- `lowerAddSubSatToAddoSubo .g_saddsat`: on overflow, the wrapped sum has the opposite sign of
`x`, so `(r >>s (w - 1)) + INT_MIN` saturates towards the sign of `x`. -/
private theorem saddSat_addo {w : Nat} (x y : Data.LLVM.Int w) :
    x.saddSat y ⊒ GMIR.selectNonzero (x.saddOverflowFlag y)
      (((x.add y).ashr (shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w (↑w - 1))))).add
        (Data.LLVM.Int.val (BitVec.ofInt w (-2 ^ (w - 1)))))
      (x.add y) := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.saddSat, Data.LLVM.Int.add, Data.LLVM.Int.saddOverflowFlag,
    GMIR.selectNonzero, Id.run, isRefinedBy_eq, pure]
  rename_i x y
  by_cases h : x.saddOverflow y <;> simp only [h, ite_true, ite_false, Bool.false_eq_true]
  · have hw : 0 < w := by
      rcases w with _ | w
      · revert h; revert x y; decide
      · omega
    have hmsb : (x + y).msb = !x.msb := by
      rw [BitVec.saddOverflow_eq] at h
      cases hx : x.msb <;> cases hy : y.msb <;> cases hs : (x + y).msb <;> simp_all
    have hlt : w - 1 < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le w 1) Nat.lt_two_pow_self
    simp [shiftAmount_width_sub_one hw, Data.LLVM.Int.ashr, Id.run, BitVec.sshiftRight_eq',
      Nat.mod_eq_of_lt hlt, Data.LLVM.sshiftRight_width_sub_one, hmsb, ← BitVec.intMin_eq_neg_two_pow,
      show ¬ w ≤ w - 1 by omega]
    cases x.msb <;> simp [Data.LLVM.allOnes_add_intMin]
  · simp

/-- `lowerAddSubSatToAddoSubo .g_ssubsat`, as `saddSat_addo`. -/
private theorem ssubSat_subo {w : Nat} (x y : Data.LLVM.Int w) :
    x.ssubSat y ⊒ GMIR.selectNonzero (x.ssubOverflowFlag y)
      (((x.sub y).ashr (shiftAmount w (Data.LLVM.Int.val (BitVec.ofInt w (↑w - 1))))).add
        (Data.LLVM.Int.val (BitVec.ofInt w (-2 ^ (w - 1)))))
      (x.sub y) := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.ssubSat, Data.LLVM.Int.sub, Data.LLVM.Int.add,
    Data.LLVM.Int.ssubOverflowFlag, GMIR.selectNonzero, Id.run, isRefinedBy_eq, pure]
  rename_i x y
  by_cases h : x.ssubOverflow y <;> simp only [h, ite_true, ite_false, Bool.false_eq_true]
  · have hw : 0 < w := by
      rcases w with _ | w
      · revert h; revert x y; decide
      · omega
    have hmsb : (x - y).msb = !x.msb := by
      rw [BitVec.ssubOverflow_eq] at h
      cases hx : x.msb <;> cases hy : y.msb <;> cases hs : (x - y).msb <;> simp_all
    have hlt : w - 1 < 2 ^ w := Nat.lt_of_le_of_lt (Nat.sub_le w 1) Nat.lt_two_pow_self
    simp [shiftAmount_width_sub_one hw, Data.LLVM.Int.ashr, Id.run, BitVec.sshiftRight_eq',
      Nat.mod_eq_of_lt hlt, Data.LLVM.sshiftRight_width_sub_one, hmsb, ← BitVec.intMin_eq_neg_two_pow,
      show ¬ w ≤ w - 1 by omega]
    cases x.msb <;> simp [Data.LLVM.allOnes_add_intMin]
  · simp

theorem custom_uaddsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_uaddsat false true) := by
  proveLegalValid using Data.LLVM.uaddSat_addo

theorem custom_usubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_usubsat false false) := by
  proveLegalValid using Data.LLVM.usubSat_subo

theorem custom_saddsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_saddsat true true) := by
  proveLegalValid using saddSat_addo

theorem custom_ssubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_ssubsat true false) := by
  proveLegalValid using ssubSat_subo

/-! ## Status of every custom legalization -/

@[legalization_status]
theorem custom_add_status :
    Status Unproven (customLegalizeWordBinary .g_addw) :=
  .proven custom_add_valid

@[legalization_status]
theorem custom_sub_status :
    Status Unproven (customLegalizeWordBinary .g_subw) :=
  .proven custom_sub_valid

@[legalization_status]
theorem custom_mul_status :
    Status Unproven (customLegalizeWordBinary .g_mulw) :=
  .proven custom_mul_valid

@[legalization_status]
theorem custom_sdiv_status :
    Status Unproven (customLegalizeWordBinary .g_divw) :=
  .proven custom_sdiv_valid

@[legalization_status]
theorem custom_udiv_status :
    Status Unproven (customLegalizeWordBinary .g_divuw) :=
  .proven custom_udiv_valid

@[legalization_status]
theorem custom_urem_status :
    Status Unproven (customLegalizeWordBinary .g_remuw) :=
  .proven custom_urem_valid

@[legalization_status]
theorem custom_shl_status :
    Status Unproven (customLegalizeWordBinary .g_sllw) :=
  .proven custom_shl_valid

@[legalization_status]
theorem custom_lshr_status :
    Status Unproven (customLegalizeWordBinary .g_srlw) :=
  .proven custom_lshr_valid

@[legalization_status]
theorem custom_ashr_status :
    Status Unproven (customLegalizeWordBinary .g_sraw) :=
  .proven custom_ashr_valid

@[legalization_status]
theorem custom_ctlz_status :
    Status Unproven (customLegalizeWordUnary .g_clzw) :=
  .proven custom_ctlz_valid

@[legalization_status]
theorem custom_cttz_status :
    Status Unproven (customLegalizeWordUnary .g_ctzw) :=
  .proven custom_cttz_valid

@[legalization_status]
theorem custom_bitreverse_status :
    Status Unproven (customLegalizeBitreverse8) :=
  .proven custom_bitreverse_valid

@[legalization_status]
theorem custom_abs_status :
    Status Unproven (customLegalizeAbs) :=
  .proven custom_abs_valid

@[legalization_status]
theorem custom_uaddsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_uaddsat false true) :=
  .proven custom_uaddsat_valid

@[legalization_status]
theorem custom_usubsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_usubsat false false) :=
  .proven custom_usubsat_valid

@[legalization_status]
theorem custom_saddsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_saddsat true true) :=
  .proven custom_saddsat_valid

@[legalization_status]
theorem custom_ssubsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_ssubsat true false) :=
  .proven custom_ssubsat_valid

end Veir.Legalization.CTreeProofs
