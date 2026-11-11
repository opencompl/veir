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

/-! CTree validity of the gMIR combines of `Veir.Passes.Legalization.CombinerHelper`.

Most combines that test the value of a matched `g_constant` read it at the width of its attribute,
which the matcher does not tie to the width of its result, hence `untypedConstant`. The shifts of
`select_into_binop_pattern` shift by `c ? k : 0`, which is poison at width 0 when `c` is false,
while the source is not. -/

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

private theorem bv_beq_comm {w : Nat} (a b : BitVec w) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact eq_comm

/-- `canonicalize_icmp_pattern`: swapping the operands of a comparison swaps its predicate. -/
private theorem icmp_swap {w : Nat} (k x : Data.LLVM.Int w) (p : Data.LLVM.IntPred) :
    k.icmp x p ⊒ x.icmp k (swapIntPred p) := by
  cases k <;> cases x <;> cases p <;>
    simp [Data.LLVM.Int.icmp, swapIntPred, Data.LLVM.IntPred.eval, Id.run, isRefinedBy_eq, bne]
  all_goals rw [bv_beq_comm]

/-- The low bit of an odd constant is set. -/
private theorem one_and_ofInt_of_odd {W : Nat} (hW : 0 < W) (v : _root_.Int) (hv : v % 2 = 1) :
    1#W &&& BitVec.ofInt W v = 1#W := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_one]
  by_cases h : i = 0
  · subst h
    simp only [decide_true, Bool.true_and, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofInt,
      Nat.testBit_zero, decide_eq_true_eq]
    have hd : (2 : _root_.Int) ∣ ((2 ^ W : Nat) : _root_.Int) := by
      refine ⟨((2 ^ (W - 1) : Nat) : _root_.Int), ?_⟩
      rw [show W = (W - 1) + 1 by omega, Nat.pow_succ]
      push_cast
      rw [_root_.Int.mul_comm]
    have h1 : (v % ((2 ^ W : Nat) : _root_.Int)) % 2 = 1 := by
      rw [_root_.Int.emod_emod_of_dvd _ hd]; exact hv
    have h0 : 0 ≤ v % ((2 ^ W : Nat) : _root_.Int) :=
      _root_.Int.emod_nonneg _ (by have := Nat.two_pow_pos W; omega)
    omega
  · simp [h]

/-- `redundant_and_pattern`, for an `i1` result: masking a comparison with an odd constant keeps it. -/
private theorem and_icmp_odd {v : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) : (x.icmp y p).and (.val (BitVec.ofInt 1 c)) ⊒ x.icmp y p := by
  have := one_and_ofInt_of_odd (W := 1) (by decide) c hc
  cases x <;> cases y <;> simp only [Data.LLVM.Int.icmp, Data.LLVM.Int.and, Id.run, isRefinedBy_eq, pure]
  rename_i a b
  cases Data.LLVM.IntPred.eval p a b <;> simp_all

/-- `redundant_and_pattern`, for a wider result: the comparison is zero-extended to `0` or `1`. -/
private theorem and_zext_icmp_odd {v W : Nat} (x y : Data.LLVM.Int v) (p : Data.LLVM.IntPred) (c : _root_.Int)
    (hc : c % 2 = 1) (hW : 1 < W) :
    ((x.icmp y p).zext W false hW).and (.val (BitVec.ofInt W c)) ⊒ (x.icmp y p).zext W false hW := by
  have := one_and_ofInt_of_odd (W := W) (by omega) c hc
  cases x <;> cases y <;>
    simp only [Data.LLVM.Int.icmp, Data.LLVM.Int.and, Data.LLVM.Int.zext, Id.run, isRefinedBy_eq, pure]
  rename_i a b
  have h1 : BitVec.setWidth W 1#1 = 1#W := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.one_mod_two_pow (by omega : 0 < W)]
  cases Data.LLVM.IntPred.eval p a b <;> simp_all [BitVec.setWidth_eq]

theorem combine_hoist_and_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_shl) := by
  proveLegalValid using Data.LLVM.hoist_and_shl

theorem combine_hoist_and_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_lshr) := by
  proveLegalValid using Data.LLVM.hoist_and_lshr

theorem combine_hoist_and_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_ashr) := by
  proveLegalValid using Data.LLVM.hoist_and_ashr

theorem combine_hoist_and_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_and) := by
  proveLegalValid using Data.LLVM.hoist_and_and

theorem combine_hoist_or_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_shl) := by
  proveLegalValid using Data.LLVM.hoist_or_shl

theorem combine_hoist_or_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_lshr) := by
  proveLegalValid using Data.LLVM.hoist_or_lshr

theorem combine_hoist_or_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_ashr) := by
  proveLegalValid using Data.LLVM.hoist_or_ashr

theorem combine_hoist_or_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_and) := by
  proveLegalValid using Data.LLVM.hoist_or_and

theorem combine_hoist_xor_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_shl) := by
  proveLegalValid using Data.LLVM.hoist_xor_shl

theorem combine_hoist_xor_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_lshr) := by
  proveLegalValid using Data.LLVM.hoist_xor_lshr

theorem combine_hoist_xor_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_ashr) := by
  proveLegalValid using Data.LLVM.hoist_xor_ashr

theorem combine_hoist_xor_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_and) := by
  proveLegalValid using Data.LLVM.hoist_xor_and

theorem combine_sub_add_reg_x_add_y_sub_y_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_y_pattern := by
  proveLegalValid using Data.LLVM.sub_add_reg_x_add_y_sub_y

theorem combine_sub_add_reg_x_add_y_sub_x_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_x_pattern := by
  proveLegalValid using Data.LLVM.sub_add_reg_x_add_y_sub_x

theorem combine_sub_add_reg_negate_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern false) := by
  proveLegalValid using Data.LLVM.sub_add_reg_negate

theorem combine_sub_add_reg_negate_x_first_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern true) := by
  proveLegalValid using Data.LLVM.sub_add_reg_negate_x_first

theorem combine_xor_of_and_with_same_reg_valid : Puddle.CTree.Pattern.Valid xor_of_and_with_same_reg_pattern := by
  proveLegalValid using Data.LLVM.xor_of_and_with_same_reg

theorem combine_trunc_of_zext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_zext) := by
  proveLegalValid using Data.LLVM.trunc_of_zext

theorem combine_trunc_of_sext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_sext) := by
  proveLegalValid using Data.LLVM.trunc_of_sext

theorem combine_redundant_add_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .eq) := by
  proveLegalValid using Data.LLVM.add_eq_self

theorem combine_redundant_add_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .ne) := by
  proveLegalValid using Data.LLVM.add_ne_self

theorem combine_redundant_sub_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .eq) := by
  proveLegalValid using Data.LLVM.sub_eq_self

theorem combine_redundant_sub_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .ne) := by
  proveLegalValid using Data.LLVM.sub_ne_self

theorem combine_redundant_xor_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .eq) := by
  proveLegalValid using Data.LLVM.xor_eq_self

theorem combine_redundant_xor_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .ne) := by
  proveLegalValid using Data.LLVM.xor_ne_self

theorem combine_combine_or_of_and_tt_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true true) := by
  proveLegalValid using Data.LLVM.combine_or_of_and_left

theorem combine_combine_or_of_and_tf_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true false) := by
  proveLegalValid using Data.LLVM.combine_or_of_and_left'

theorem combine_combine_or_of_and_ft_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false true) := by
  proveLegalValid using Data.LLVM.combine_or_of_and_right

theorem combine_combine_or_of_and_ff_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false false) := by
  proveLegalValid using Data.LLVM.combine_or_of_and_right'

theorem combine_AMinusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusC_pattern := by
  proveLegalValid using Data.LLVM.AMinusBMinusC

theorem combine_zext_of_zext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_zext) := by
  proveLegalValid using Data.LLVM.zext_of_zext

theorem combine_sext_of_sext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_sext) := by
  proveLegalValid using Data.LLVM.sext_of_sext

theorem combine_canonicalize_icmp_valid : Puddle.CTree.Pattern.Valid canonicalize_icmp_pattern := by
  proveLegalValid using icmp_swap

theorem combine_bitreverse_shl_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_shl .g_lshr) := by
  proveLegalValid using Data.LLVM.bitreverse_shl

theorem combine_bitreverse_lshr_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_lshr .g_shl) := by
  proveLegalValid using Data.LLVM.bitreverse_lshr

theorem combine_binop_same_val_and_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_and) := by
  proveLegalValid using Data.LLVM.binop_same_val_and

theorem combine_binop_same_val_or_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_or) := by
  proveLegalValid using Data.LLVM.binop_same_val_or

theorem combine_same_val_zero_sub_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_sub) := by
  proveLegalValid using Data.LLVM.same_val_zero_sub

theorem combine_same_val_zero_xor_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_xor) := by
  proveLegalValid using Data.LLVM.same_val_zero_xor

theorem combine_add_sub_reg_0_valid : Puddle.CTree.Pattern.Valid add_sub_reg_0_pattern := by
  proveLegalValid using Data.LLVM.add_sub_reg_0

theorem combine_add_sub_reg_1_valid : Puddle.CTree.Pattern.Valid add_sub_reg_1_pattern := by
  proveLegalValid using Data.LLVM.add_sub_reg_1

theorem combine_APlusBMinusCMinusB_valid : Puddle.CTree.Pattern.Valid APlusBMinusCMinusB_pattern := by
  proveLegalValid using Data.LLVM.APlusBMinusCMinusB

theorem combine_AMinusBMinusCMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusCMinusC_pattern := by
  proveLegalValid using Data.LLVM.AMinusBMinusCMinusC

theorem combine_AMinusBPlusCMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBPlusCMinusA_pattern := by
  proveLegalValid using Data.LLVM.AMinusBPlusCMinusA

theorem combine_AMinusBPlusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBPlusBMinusC_pattern := by
  proveLegalValid using Data.LLVM.AMinusBPlusBMinusC

theorem combine_AMinusBMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBMinusA_pattern := by
  proveLegalValid using Data.LLVM.AMinusBMinusA

theorem combine_APlusBMinusAPlusC_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern true) := by
  proveLegalValid using Data.LLVM.APlusBMinusAPlusC

theorem combine_APlusBMinusCPlusA_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern false) := by
  proveLegalValid using Data.LLVM.APlusBMinusCPlusA

theorem combine_select_same_val_valid : Puddle.CTree.Pattern.Valid select_same_val_pattern := by
  proveLegalValid using Data.LLVM.select_same_val

theorem combine_select_ugt_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ugt .g_umax) := by
  proveLegalValid using Data.LLVM.select_ugt_umax

theorem combine_select_uge_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .uge .g_umax) := by
  proveLegalValid using Data.LLVM.select_uge_umax

theorem combine_select_sgt_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sgt .g_smax) := by
  proveLegalValid using Data.LLVM.select_sgt_smax

theorem combine_select_sge_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sge .g_smax) := by
  proveLegalValid using Data.LLVM.select_sge_smax

theorem combine_select_ult_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ult .g_umin) := by
  proveLegalValid using Data.LLVM.select_ult_umin

theorem combine_select_ule_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ule .g_umin) := by
  proveLegalValid using Data.LLVM.select_ule_umin

theorem combine_select_slt_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .slt .g_smin) := by
  proveLegalValid using Data.LLVM.select_slt_smin

theorem combine_select_sle_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sle .g_smin) := by
  proveLegalValid using Data.LLVM.select_sle_smin

theorem combine_zext_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_zext) := by
  proveLegalValid using Data.LLVM.zext_of_select

theorem combine_trunc_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_trunc) := by
  proveLegalValid using Data.LLVM.trunc_of_select

theorem combine_select_into_sub_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub false) := by
  proveLegalValid using Data.LLVM.select_into_sub'

theorem combine_select_into_sub_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub true) := by
  proveLegalValid using Data.LLVM.select_into_sub_swapped

theorem combine_select_into_add_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add false) := by
  proveLegalValid using Data.LLVM.select_into_add'

theorem combine_select_into_add_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add true) := by
  proveLegalValid using Data.LLVM.select_into_add_swapped

theorem combine_select_into_or_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or false) := by
  proveLegalValid using Data.LLVM.select_into_or'

theorem combine_select_into_or_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or true) := by
  proveLegalValid using Data.LLVM.select_into_or_swapped

theorem combine_select_into_xor_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor false) := by
  proveLegalValid using Data.LLVM.select_into_xor'

theorem combine_select_into_xor_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor true) := by
  proveLegalValid using Data.LLVM.select_into_xor_swapped

/-- `redundant_and_select_pattern .icmp .icmp`, for an `i1` result: both arms are comparisons. -/
private theorem and_select_icmp_odd {wc v₁ v₂ : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) :
    (GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q)).and (.val (BitVec.ofInt 1 k)) ⊒
      GMIR.selectNonzero c (x.icmp y p) (x'.icmp y' q) := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Data.LLVM.Int.and, Id.run, poison_isRefinedBy]
  | val c =>
    by_cases h : c = 0#wc <;> simp only [GMIR.selectNonzero, Id.run, h, bne_self_eq_false, ite_false,
      ite_true, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true]
    · exact and_icmp_odd x' y' q k hk
    · exact and_icmp_odd x y p k hk

/-- `redundant_and_select_pattern .icmp .icmp`, for a wider result. -/
private theorem and_select_zext_icmp_odd {wc v₁ v₂ W : Nat} (c : Data.LLVM.Int wc) (x y : Data.LLVM.Int v₁)
    (x' y' : Data.LLVM.Int v₂) (p q : Data.LLVM.IntPred) (k : _root_.Int) (hk : k % 2 = 1) (hW : 1 < W) :
    (GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW)).and
        (.val (BitVec.ofInt W k)) ⊒
      GMIR.selectNonzero c ((x.icmp y p).zext W false hW) ((x'.icmp y' q).zext W false hW) := by
  cases c with
  | poison => simp [GMIR.selectNonzero, Data.LLVM.Int.and, Id.run, poison_isRefinedBy]
  | val c =>
    by_cases h : c = 0#wc <;> simp only [GMIR.selectNonzero, Id.run, h, bne_self_eq_false, ite_false,
      ite_true, bne_iff_ne, ne_eq, not_false_eq_true, Bool.false_eq_true]
    · exact and_zext_icmp_odd x' y' q k hk hW
    · exact and_zext_icmp_odd x y p k hk hW

set_option maxHeartbeats 8000000 in
/-- The two comparisons and the constant make this the slowest combine to normalize. -/
theorem combine_redundant_and_select_icmp_icmp_valid :
    Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .icmp) := by
  proveLegalValid with first
    | (apply and_select_zext_icmp_odd <;> assumption)
    | (apply and_select_icmp_odd <;> assumption)

theorem combine_redundant_and_valid : Puddle.CTree.Pattern.Valid redundant_and_pattern := by
  proveLegalValid with first
    | (apply and_zext_icmp_odd <;> assumption)
    | (apply and_icmp_odd <;> assumption)

/-! ### Funnel shifts or-ed with the shift they subsume

`(fshl x z y) | (x << y) → fshl x z y` and `(z >> y) | (fshr x z y) → fshr x z y`, in both orders:
the plain shift's bits are among the funnel shift's when the amount is in range, and it is poison
otherwise. -/

/-- The bits of `x << s` are among those of `fshl x z s`, for `s < w`. -/
private theorem fshl_or_shl_bits {w : Nat} (x z : BitVec w) (s : Nat) :
    ((x ++ z) <<< s).extractLsb' w w ||| x <<< s = ((x ++ z) <<< s).extractLsb' w w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_extractLsb', BitVec.getElem_shiftLeft,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append]
  by_cases h : i < s
  · simp [h]
  · have : ¬ w + i < s := by omega
    simp only [h, this, decide_false, Bool.not_false, Bool.true_and, show w + i < w + w by omega,
      decide_true, show ¬ (w + i - s < w) by omega, ite_false, BitVec.getLsbD_eq_getElem (by omega : i - s < w),
      show w + i - s - w = i - s by omega]
    simp

/-- The bits of `z >> s` are among those of `fshr x z s`. -/
private theorem lshr_or_fshr_bits {w : Nat} (x z : BitVec w) (s : Nat) :
    z >>> s ||| ((x ++ z) >>> s).truncate w = ((x ++ z) >>> s).truncate w := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_ushiftRight, BitVec.truncate_eq_setWidth,
    BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append]
  by_cases h : s + i < w
  · simp [h]
  · simp [BitVec.getLsbD_of_ge z (s + i) (by omega)]

private theorem fshl_or_shl {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (n u d : Bool) :
    (x.fshl z (GMIR.funnelShiftAmount w y)).or (x.shl (shiftAmount w y) n u) d ⊒
      x.fshl z (GMIR.funnelShiftAmount w y) := by
  cases x <;> cases z <;> cases y <;>
    simp [GMIR.funnelShiftAmount, shiftAmount, Data.LLVM.Int.fshl, Data.LLVM.Int.shl, Data.LLVM.Int.or,
      Id.run, poison_isRefinedBy, pure]
  rename_i x z y
  by_cases h : y.toNat < w
  · have hw : w < 2 ^ w := Nat.lt_two_pow_self
    have hsw : (BitVec.setWidth w y).toNat = y.toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by omega)
    have hm : y.toNat % w % 2 ^ w % w = y.toNat := by
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show y.toNat < 2 ^ w by omega), Nat.mod_eq_of_lt h]
    have hlt : ¬ BitVec.ofNat w w ≤ BitVec.setWidth w y := by
      simp only [BitVec.le_def, hsw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      omega
    simp only [h, ite_true, hlt, ite_false, hsw, hm]
    split
    · rename_i y' heq
      simp only [Data.LLVM.ite_poison_eq_val_id, Data.LLVM.val_eq_val_id] at heq
      obtain ⟨-, -, rfl⟩ := heq
      split <;> simp [poison_isRefinedBy, isRefinedBy_eq, fshl_or_shl_bits]
    · simp [poison_isRefinedBy]
  · have hge : BitVec.ofNat w w ≤ BitVec.allOnes w := by
      have := Nat.lt_two_pow_self (n := w)
      simp [BitVec.le_def, BitVec.toNat_allOnes, Nat.mod_eq_of_lt this]
      omega
    simp [h, hge, poison_isRefinedBy]

private theorem lshr_or_fshr {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (e d : Bool) :
    (z.lshr (shiftAmount w y) e).or (x.fshr z (GMIR.funnelShiftAmount w y)) d ⊒
      x.fshr z (GMIR.funnelShiftAmount w y) := by
  cases x <;> cases z <;> cases y <;>
    simp [GMIR.funnelShiftAmount, shiftAmount, Data.LLVM.Int.fshr, Data.LLVM.Int.lshr, Data.LLVM.Int.or,
      Id.run, poison_isRefinedBy, pure]
  case poison.val.val => split <;> simp [poison_isRefinedBy]
  rename_i x z y
  by_cases h : y.toNat < w
  · have hw : w < 2 ^ w := Nat.lt_two_pow_self
    have hsw : (BitVec.setWidth w y).toNat = y.toNat := by
      simp only [BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by omega)
    have hm : y.toNat % w % 2 ^ w % w = y.toNat := by
      rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show y.toNat < 2 ^ w by omega), Nat.mod_eq_of_lt h]
    have hlt : ¬ BitVec.ofNat w w ≤ BitVec.setWidth w y := by
      simp only [BitVec.le_def, hsw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]
      omega
    simp only [h, ite_true, hlt, ite_false, hsw, hm]
    split
    · rename_i y' heq
      simp only [Data.LLVM.ite_poison_eq_val_id, Data.LLVM.val_eq_val_id] at heq
      obtain ⟨-, rfl⟩ := heq
      split <;> simp [poison_isRefinedBy, isRefinedBy_eq, lshr_or_fshr_bits]
    · simp [poison_isRefinedBy]
  · have hge : BitVec.ofNat w w ≤ BitVec.allOnes w := by
      have := Nat.lt_two_pow_self (n := w)
      simp [BitVec.le_def, BitVec.toNat_allOnes, Nat.mod_eq_of_lt this]
      omega
    simp [h, hge, poison_isRefinedBy]

/-- `g_or` is commutative, including its `disjoint` check. -/
private theorem or_comm' {w : Nat} (a b : Data.LLVM.Int w) (d : Bool) : a.or b d = b.or a d := by
  cases a <;> cases b <;> simp [Data.LLVM.Int.or, Id.run, BitVec.or_comm, BitVec.and_comm]

private theorem shl_or_fshl {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (n u d : Bool) :
    (x.shl (shiftAmount w y) n u).or (x.fshl z (GMIR.funnelShiftAmount w y)) d ⊒
      x.fshl z (GMIR.funnelShiftAmount w y) := by
  rw [or_comm']
  exact fshl_or_shl x z y n u d

private theorem fshr_or_lshr {w v : Nat} (x z : Data.LLVM.Int w) (y : Data.LLVM.Int v) (e d : Bool) :
    (x.fshr z (GMIR.funnelShiftAmount w y)).or (z.lshr (shiftAmount w y) e) d ⊒
      x.fshr z (GMIR.funnelShiftAmount w y) := by
  rw [or_comm']
  exact lshr_or_fshr x z y e d

theorem combine_funnel_shift_fshl_or_shl_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) := by
  proveLegalValid using fshl_or_shl

theorem combine_funnel_shift_shl_or_fshl_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) := by
  proveLegalValid using shl_or_fshl

theorem combine_funnel_shift_fshr_or_lshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) := by
  proveLegalValid using fshr_or_lshr

theorem combine_funnel_shift_lshr_or_fshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) := by
  proveLegalValid using lshr_or_fshr

/-! ## Status of every combine -/

@[legalization_status]
theorem combine_hoist_and_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_shl) :=
  .proven (combine_hoist_and_shl_valid )

@[legalization_status]
theorem combine_hoist_and_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_lshr) :=
  .proven (combine_hoist_and_lshr_valid )

@[legalization_status]
theorem combine_hoist_and_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_ashr) :=
  .proven (combine_hoist_and_ashr_valid )

@[legalization_status]
theorem combine_hoist_and_and_status :
    Status Unproven (hoist_logic_op_pattern .g_and .g_and) :=
  .proven (combine_hoist_and_and_valid )

@[legalization_status]
theorem combine_hoist_or_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_shl) :=
  .proven (combine_hoist_or_shl_valid )

@[legalization_status]
theorem combine_hoist_or_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_lshr) :=
  .proven (combine_hoist_or_lshr_valid )

@[legalization_status]
theorem combine_hoist_or_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_ashr) :=
  .proven (combine_hoist_or_ashr_valid )

@[legalization_status]
theorem combine_hoist_or_and_status :
    Status Unproven (hoist_logic_op_pattern .g_or .g_and) :=
  .proven (combine_hoist_or_and_valid )

@[legalization_status]
theorem combine_hoist_xor_shl_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_shl) :=
  .proven (combine_hoist_xor_shl_valid )

@[legalization_status]
theorem combine_hoist_xor_lshr_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_lshr) :=
  .proven (combine_hoist_xor_lshr_valid )

@[legalization_status]
theorem combine_hoist_xor_ashr_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_ashr) :=
  .proven (combine_hoist_xor_ashr_valid )

@[legalization_status]
theorem combine_hoist_xor_and_status :
    Status Unproven (hoist_logic_op_pattern .g_xor .g_and) :=
  .proven (combine_hoist_xor_and_valid )

@[legalization_status]
theorem combine_sub_add_reg_x_add_y_sub_y_status :
    Status Unproven sub_add_reg_x_add_y_sub_y_pattern :=
  .proven (combine_sub_add_reg_x_add_y_sub_y_valid )

@[legalization_status]
theorem combine_sub_add_reg_x_add_y_sub_x_status :
    Status Unproven sub_add_reg_x_add_y_sub_x_pattern :=
  .proven (combine_sub_add_reg_x_add_y_sub_x_valid )

@[legalization_status]
theorem combine_sub_add_reg_negate_status :
    Status Unproven (sub_add_reg_negate_pattern false) :=
  .proven (combine_sub_add_reg_negate_valid )

@[legalization_status]
theorem combine_sub_add_reg_negate_x_first_status :
    Status Unproven (sub_add_reg_negate_pattern true) :=
  .proven (combine_sub_add_reg_negate_x_first_valid )

@[legalization_status]
theorem combine_xor_of_and_with_same_reg_status :
    Status Unproven xor_of_and_with_same_reg_pattern :=
  .proven (combine_xor_of_and_with_same_reg_valid )

@[legalization_status]
theorem combine_trunc_of_zext_status :
    Status Unproven (trunc_of_ext_pattern .g_zext) :=
  .proven (combine_trunc_of_zext_valid )

@[legalization_status]
theorem combine_trunc_of_sext_status :
    Status Unproven (trunc_of_ext_pattern .g_sext) :=
  .proven (combine_trunc_of_sext_valid )

@[legalization_status]
theorem combine_redundant_add_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_add .eq) :=
  .proven (combine_redundant_add_eq_valid )

@[legalization_status]
theorem combine_redundant_add_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_add .ne) :=
  .proven (combine_redundant_add_ne_valid )

@[legalization_status]
theorem combine_redundant_sub_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_sub .eq) :=
  .proven (combine_redundant_sub_eq_valid )

@[legalization_status]
theorem combine_redundant_sub_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_sub .ne) :=
  .proven (combine_redundant_sub_ne_valid )

@[legalization_status]
theorem combine_redundant_xor_eq_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_xor .eq) :=
  .proven (combine_redundant_xor_eq_valid )

@[legalization_status]
theorem combine_redundant_xor_ne_status :
    Status Unproven (redundant_binop_in_equality_pattern .g_xor .ne) :=
  .proven (combine_redundant_xor_ne_valid )

@[legalization_status]
theorem combine_combine_or_of_and_tt_status :
    Status Unproven (combine_or_of_and_pattern true true) :=
  .proven (combine_combine_or_of_and_tt_valid )

@[legalization_status]
theorem combine_combine_or_of_and_tf_status :
    Status Unproven (combine_or_of_and_pattern true false) :=
  .proven (combine_combine_or_of_and_tf_valid )

@[legalization_status]
theorem combine_combine_or_of_and_ft_status :
    Status Unproven (combine_or_of_and_pattern false true) :=
  .proven (combine_combine_or_of_and_ft_valid )

@[legalization_status]
theorem combine_combine_or_of_and_ff_status :
    Status Unproven (combine_or_of_and_pattern false false) :=
  .proven (combine_combine_or_of_and_ff_valid )

@[legalization_status]
theorem combine_AMinusBMinusC_status :
    Status Unproven AMinusBMinusC_pattern :=
  .proven (combine_AMinusBMinusC_valid )

@[legalization_status]
theorem combine_zext_of_zext_status :
    Status Unproven (ext_of_ext_pattern .g_zext) :=
  .proven (combine_zext_of_zext_valid )

@[legalization_status]
theorem combine_sext_of_sext_status :
    Status Unproven (ext_of_ext_pattern .g_sext) :=
  .proven (combine_sext_of_sext_valid )

@[legalization_status]
theorem combine_canonicalize_icmp_status :
    Status Unproven canonicalize_icmp_pattern :=
  .proven (combine_canonicalize_icmp_valid )

@[legalization_status]
theorem combine_bitreverse_shl_status :
    Status Unproven (bitreverse_shift_pattern .g_shl .g_lshr) :=
  .proven (combine_bitreverse_shl_valid )

@[legalization_status]
theorem combine_bitreverse_lshr_status :
    Status Unproven (bitreverse_shift_pattern .g_lshr .g_shl) :=
  .proven (combine_bitreverse_lshr_valid )

@[legalization_status]
theorem combine_binop_same_val_and_status :
    Status Unproven (binop_same_val_pattern .g_and) :=
  .proven (combine_binop_same_val_and_valid )

@[legalization_status]
theorem combine_binop_same_val_or_status :
    Status Unproven (binop_same_val_pattern .g_or) :=
  .proven (combine_binop_same_val_or_valid )

@[legalization_status]
theorem combine_same_val_zero_sub_status :
    Status Unproven (same_val_zero_pattern .g_sub) :=
  .proven (combine_same_val_zero_sub_valid )

@[legalization_status]
theorem combine_same_val_zero_xor_status :
    Status Unproven (same_val_zero_pattern .g_xor) :=
  .proven (combine_same_val_zero_xor_valid )

@[legalization_status]
theorem combine_add_sub_reg_0_status :
    Status Unproven add_sub_reg_0_pattern :=
  .proven (combine_add_sub_reg_0_valid )

@[legalization_status]
theorem combine_add_sub_reg_1_status :
    Status Unproven add_sub_reg_1_pattern :=
  .proven (combine_add_sub_reg_1_valid )

@[legalization_status]
theorem combine_APlusBMinusCMinusB_status :
    Status Unproven APlusBMinusCMinusB_pattern :=
  .proven (combine_APlusBMinusCMinusB_valid )

@[legalization_status]
theorem combine_AMinusBMinusCMinusC_status :
    Status Unproven AMinusBMinusCMinusC_pattern :=
  .proven (combine_AMinusBMinusCMinusC_valid )

@[legalization_status]
theorem combine_AMinusBPlusCMinusA_status :
    Status Unproven AMinusBPlusCMinusA_pattern :=
  .proven (combine_AMinusBPlusCMinusA_valid )

@[legalization_status]
theorem combine_AMinusBPlusBMinusC_status :
    Status Unproven AMinusBPlusBMinusC_pattern :=
  .proven (combine_AMinusBPlusBMinusC_valid )

@[legalization_status]
theorem combine_AMinusBMinusA_status :
    Status Unproven AMinusBMinusA_pattern :=
  .proven (combine_AMinusBMinusA_valid )

@[legalization_status]
theorem combine_APlusBMinusAPlusC_status :
    Status Unproven (APlusBMinusAPlusC_pattern true) :=
  .proven (combine_APlusBMinusAPlusC_valid )

@[legalization_status]
theorem combine_APlusBMinusCPlusA_status :
    Status Unproven (APlusBMinusAPlusC_pattern false) :=
  .proven (combine_APlusBMinusCPlusA_valid )

@[legalization_status]
theorem combine_select_same_val_status :
    Status Unproven select_same_val_pattern :=
  .proven (combine_select_same_val_valid )

@[legalization_status]
theorem combine_select_ugt_umax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ugt .g_umax) :=
  .proven (combine_select_ugt_umax_valid info )

@[legalization_status]
theorem combine_select_uge_umax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .uge .g_umax) :=
  .proven (combine_select_uge_umax_valid info )

@[legalization_status]
theorem combine_select_sgt_smax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sgt .g_smax) :=
  .proven (combine_select_sgt_smax_valid info )

@[legalization_status]
theorem combine_select_sge_smax_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sge .g_smax) :=
  .proven (combine_select_sge_smax_valid info )

@[legalization_status]
theorem combine_select_ult_umin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ult .g_umin) :=
  .proven (combine_select_ult_umin_valid info )

@[legalization_status]
theorem combine_select_ule_umin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .ule .g_umin) :=
  .proven (combine_select_ule_umin_valid info )

@[legalization_status]
theorem combine_select_slt_smin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .slt .g_smin) :=
  .proven (combine_select_slt_smin_valid info )

@[legalization_status]
theorem combine_select_sle_smin_status (info : LegalizerInfo) :
    Status Unproven (select_to_iminmax_pattern info .sle .g_smin) :=
  .proven (combine_select_sle_smin_valid info )

@[legalization_status]
theorem combine_zext_of_select_status (info : LegalizerInfo) :
    Status Unproven (select_of_cast_pattern info .g_zext) :=
  .proven (combine_zext_of_select_valid info )

@[legalization_status]
theorem combine_trunc_of_select_status (info : LegalizerInfo) :
    Status Unproven (select_of_cast_pattern info .g_trunc) :=
  .proven (combine_trunc_of_select_valid info )

@[legalization_status]
theorem combine_select_into_sub_status :
    Status Unproven (select_into_binop_pattern .g_sub false) :=
  .proven (combine_select_into_sub_valid )

@[legalization_status]
theorem combine_select_into_sub_swapped_status :
    Status Unproven (select_into_binop_pattern .g_sub true) :=
  .proven (combine_select_into_sub_swapped_valid )

@[legalization_status]
theorem combine_select_into_add_status :
    Status Unproven (select_into_binop_pattern .g_add false) :=
  .proven (combine_select_into_add_valid )

@[legalization_status]
theorem combine_select_into_add_swapped_status :
    Status Unproven (select_into_binop_pattern .g_add true) :=
  .proven (combine_select_into_add_swapped_valid )

@[legalization_status]
theorem combine_select_into_or_status :
    Status Unproven (select_into_binop_pattern .g_or false) :=
  .proven (combine_select_into_or_valid )

@[legalization_status]
theorem combine_select_into_or_swapped_status :
    Status Unproven (select_into_binop_pattern .g_or true) :=
  .proven (combine_select_into_or_swapped_valid )

@[legalization_status]
theorem combine_select_into_xor_status :
    Status Unproven (select_into_binop_pattern .g_xor false) :=
  .proven (combine_select_into_xor_valid )

@[legalization_status]
theorem combine_select_into_xor_swapped_status :
    Status Unproven (select_into_binop_pattern .g_xor true) :=
  .proven (combine_select_into_xor_swapped_valid )

@[legalization_status]
theorem combine_redundant_and_status : Status Unproven redundant_and_pattern :=
  .proven combine_redundant_and_valid

@[legalization_status]
theorem combine_sub_to_add_status (info : LegalizerInfo) :
    Status Unproven (sub_to_add_pattern info) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_redundant_and_select_icmp_icmp_status :
    Status Unproven (redundant_and_select_pattern .icmp .icmp) :=
  .proven combine_redundant_and_select_icmp_icmp_valid

@[legalization_status]
theorem combine_redundant_and_select_icmp_constant_status :
    Status Unproven (redundant_and_select_pattern .icmp .constant) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_redundant_and_select_constant_icmp_status :
    Status Unproven (redundant_and_select_pattern .constant .icmp) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_redundant_and_select_constant_constant_status :
    Status Unproven (redundant_and_select_pattern .constant .constant) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_right_identity_zero_status (opcode : GMIR) :
    Status Unproven (right_identity_zero_pattern opcode) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_right_identity_one_int_status :
    Status Unproven right_identity_one_int_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_binop_right_to_zero_status :
    Status Unproven binop_right_to_zero_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_binop_left_to_zero_status (opcode : GMIR) :
    Status Unproven (binop_left_to_zero_pattern opcode) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_sub_minus_one_status :
    Status Unproven sub_minus_one_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_ZeroMinusAPlusB_status :
    Status Unproven ZeroMinusAPlusB_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_APlusZeroMinusB_status :
    Status Unproven APlusZeroMinusB_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_AMinusZeroMinusB_status :
    Status Unproven AMinusZeroMinusB_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_sub_one_from_sub_status :
    Status Unproven sub_one_from_sub_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_APlusC1MinusC2_status :
    Status Unproven APlusC1MinusC2_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_C2MinusAPlusC1_status :
    Status Unproven C2MinusAPlusC1_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_AMinusC1MinusC2_status :
    Status Unproven AMinusC1MinusC2_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_C1MinusAMinusC2_status :
    Status Unproven C1MinusAMinusC2_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_AMinusC1PlusC2_status :
    Status Unproven AMinusC1PlusC2_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_sub_of_mul_const_status :
    Status Unproven sub_of_mul_const_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_mul_by_neg_one_status :
    Status Unproven mul_by_neg_one_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_mulo_by_2_status :
    Status Unproven mulo_by_2_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_add_shift_status (shiftFirst : Bool) :
    Status Unproven (add_shift_pattern shiftFirst) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_NotAPlusNegOne_status :
    Status Unproven NotAPlusNegOne_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_or_and_xor_to_or_status (outer inner : GMIR) :
    Status Unproven (or_and_xor_to_or_pattern outer inner) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_status (outer inner : GMIR) :
    Status Unproven (or_and_xor_to_xor_or_pattern outer inner) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_simplify_neg_minmax_status (minmax opposite : GMIR) :
    Status Unproven (simplify_neg_minmax_pattern minmax opposite) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_not_cmp_fold_status (pred inverse : Data.LLVM.IntPred) :
    Status Unproven (not_cmp_fold_pattern pred inverse) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_double_icmp_zero_status (logic : GMIR) (pred : Data.LLVM.IntPred) :
    Status Unproven (double_icmp_zero_pattern logic pred) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_udiv_by_pow2_status :
    Status Unproven udiv_by_pow2_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_sdiv_exact_by_pow2_status (negative : Bool) :
    Status Unproven (sdiv_exact_by_pow2_pattern negative) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_sdiv_by_pow2_status (negative : Bool) :
    Status Unproven (sdiv_by_pow2_pattern negative) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_mul_to_shl_status :
    Status Unproven mul_to_shl_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_urem_pow2_to_mask_status :
    Status Unproven urem_pow2_to_mask_pattern :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_constant_fold_binop_status (opcode : GMIR) (fold : _root_.Int → _root_.Int → _root_.Int) :
    Status Unproven (constant_fold_binop_pattern opcode fold) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_select_constant_cmp_status (nonzero : Bool) :
    Status Unproven (select_constant_cmp_pattern nonzero) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_select_of_constants_status (pred : GMIRConstantProperties → GMIRConstantProperties → Bool)
    (rewrite : SelectOfConstants → CreateProg.Builder CreatedOpHandle) :
    Status Unproven (select_of_constants_pattern pred rewrite) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_select_into_shl_status (swapped : Bool) :
    Status Unproven (select_into_binop_pattern .g_shl swapped) :=
  .unproven .widthDependent

@[legalization_status]
theorem combine_select_into_lshr_status (swapped : Bool) :
    Status Unproven (select_into_binop_pattern .g_lshr swapped) :=
  .unproven .widthDependent

@[legalization_status]
theorem combine_select_into_ashr_status (swapped : Bool) :
    Status Unproven (select_into_binop_pattern .g_ashr swapped) :=
  .unproven .widthDependent

@[legalization_status]
theorem combine_funnel_shift_zero_status (fsh : GMIR) (keepRight : Bool) :
    Status Unproven (funnel_shift_zero_pattern fsh keepRight) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_funnel_shift_overshift_status (fsh : GMIR) :
    Status Unproven (funnel_shift_overshift_pattern fsh) :=
  .unproven .untypedConstant

@[legalization_status]
theorem combine_funnel_shift_fshl_or_shl_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) :=
  .proven combine_funnel_shift_fshl_or_shl_valid

@[legalization_status]
theorem combine_funnel_shift_shl_or_fshl_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) :=
  .proven combine_funnel_shift_shl_or_fshl_valid

@[legalization_status]
theorem combine_funnel_shift_fshr_or_lshr_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) :=
  .proven combine_funnel_shift_fshr_or_lshr_valid

@[legalization_status]
theorem combine_funnel_shift_lshr_or_fshr_status :
    Status Unproven (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) :=
  .proven combine_funnel_shift_lshr_or_fshr_valid


end Veir.Legalization.CTreeProofs
