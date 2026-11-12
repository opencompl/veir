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
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Passes.Legalization.Validity.PBVNormalize
import all Veir.Data.Refinement
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.PBVDecide

/-!
# CTree validity of the gMIR combines that match constants (`Validity/CombineConstant`) by `pbv_decide`

Each rule is proven by `proveLegalValid with pbvClose` alone. Where the matcher leaves the
widths unbounded, the side goals `w ≤ 64` are assumed with `sorry`, so such a theorem is proven
up to 64 bits only. The rules `pbvClose` does not prove are commented out, with the reason it
fails.
-/
set_option Elab.async false
namespace Veir.Legalization.CTreeProofs.PBV

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr

/-- Close a normalized value goal by `pbv_decide 64`, assuming the width bounds it cannot derive. -/
macro "pbvClose" : tactic => `(tactic| ((veir_bv_normalize <;> pbv_decide 64 (blastWidth := 64))))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_sub_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_sub) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_add_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_add) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_or_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_or) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_xor_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_xor) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_shl_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_shl) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_ashr_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_ashr) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_zero_lshr_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_lshr) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_one_int_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_binop_right_to_zero_valid :
--     Puddle.CTree.Pattern.Valid (binop_right_to_zero_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_binop_left_to_zero_shl_valid :
--     Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_shl) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_binop_left_to_zero_lshr_valid :
--     Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_lshr) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_binop_left_to_zero_ashr_valid :
--     Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_ashr) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_binop_left_to_zero_mul_valid :
--     Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_mul) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_minus_one_valid :
--     Puddle.CTree.Pattern.Valid (sub_minus_one_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_ZeroMinusAPlusB_valid :
--     Puddle.CTree.Pattern.Valid (ZeroMinusAPlusB_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_APlusZeroMinusB_valid :
--     Puddle.CTree.Pattern.Valid (APlusZeroMinusB_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_AMinusZeroMinusB_valid :
--     Puddle.CTree.Pattern.Valid (AMinusZeroMinusB_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_one_from_sub_valid :
--     Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_APlusC1MinusC2_valid :
--     Puddle.CTree.Pattern.Valid (APlusC1MinusC2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_C2MinusAPlusC1_valid :
--     Puddle.CTree.Pattern.Valid (C2MinusAPlusC1_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_AMinusC1MinusC2_valid :
--     Puddle.CTree.Pattern.Valid (AMinusC1MinusC2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_C1MinusAMinusC2_valid :
--     Puddle.CTree.Pattern.Valid (C1MinusAMinusC2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_AMinusC1PlusC2_valid :
--     Puddle.CTree.Pattern.Valid (AMinusC1PlusC2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_of_mul_const_valid :
--     Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_by_neg_one_valid :
--     Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mulo_by_2_valid :
--     Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_NotAPlusNegOne_valid :
--     Puddle.CTree.Pattern.Valid (NotAPlusNegOne_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_add_shift_valid :
--     Puddle.CTree.Pattern.Valid (add_shift_pattern false) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_add_shift_swapped_valid :
--     Puddle.CTree.Pattern.Valid (add_shift_pattern true) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_or_and_xor_to_or_or_and_valid :
--     Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_or .g_and) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_or_and_xor_to_or_and_or_valid :
--     Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_and .g_or) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_or_and_xor_to_xor_or_or_and_valid :
--     Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_or .g_and) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_or_and_xor_to_xor_or_and_or_valid :
--     Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_and .g_or) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_simplify_neg_smax_valid :
--     Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smax .g_smin) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_simplify_neg_umax_valid :
--     Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umax .g_umin) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_simplify_neg_smin_valid :
--     Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smin .g_smax) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_simplify_neg_umin_valid :
--     Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umin .g_umax) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_eq_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ne_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ugt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_uge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ult_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ule_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sgt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_slt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sle_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_double_icmp_zero_and_valid :
--     Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_and .eq) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_double_icmp_zero_or_valid :
--     Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_or .ne) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_udiv_by_pow2_valid :
--     Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_to_shl_valid :
--     Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_urem_pow2_to_mask_valid :
--     Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_constant_fold_add_valid :
--     Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_add (fun a b => a + b)) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_constant_fold_sub_valid :
--     Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_sub ((· - ·))) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_constant_fold_mul_valid :
--     Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_mul ((· * ·))) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_constant_fold_smin_valid :
--     Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smin (min)) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_constant_fold_smax_valid :
--     Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smax (max)) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_constant_cmp_nonzero_valid :
--     Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern true) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_constant_cmp_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern false) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_to_add_valid (info : LegalizerInfo) :
--     Puddle.CTree.Pattern.Valid (sub_to_add_pattern info) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_icmp_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
--   proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_shl_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_shl_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_lshr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_lshr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_ashr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_ashr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_one_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_one_zero_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_allOnes_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_allOnes_zero_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_zero_one_valid :
--     Puddle.CTree.Pattern.Valid (select_zero_one_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_zero_allOnes_valid :
--     Puddle.CTree.Pattern.Valid (select_zero_allOnes_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_succ_valid :
--     Puddle.CTree.Pattern.Valid (select_succ_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_pred_valid :
--     Puddle.CTree.Pattern.Valid (select_pred_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_pow2_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_zero_pow2_valid :
--     Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_allOnes_const_valid :
--     Puddle.CTree.Pattern.Valid (select_allOnes_const_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_const_allOnes_valid :
--     Puddle.CTree.Pattern.Valid (select_const_allOnes_pattern) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_right_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
--   proveLegalValid with pbvClose

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_left_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
--   proveLegalValid with pbvClose

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_l_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
--   proveLegalValid with pbvClose

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_r_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
--   proveLegalValid with pbvClose

end Veir.Legalization.CTreeProofs.PBV
