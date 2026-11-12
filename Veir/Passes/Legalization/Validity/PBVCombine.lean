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
# CTree validity of the gMIR combines (`Validity/Combine`) by `pbv_decide`

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

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_and_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_shl) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_and_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_lshr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_and_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_ashr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

theorem combine_hoist_and_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_and .g_and) := by
  proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_or_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_shl) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_or_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_lshr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_or_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_ashr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

theorem combine_hoist_or_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_or .g_and) := by
  proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_xor_shl_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_shl) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_xor_lshr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_lshr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_hoist_xor_ashr_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_ashr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

theorem combine_hoist_xor_and_valid : Puddle.CTree.Pattern.Valid (hoist_logic_op_pattern .g_xor .g_and) := by
  proveLegalValid with pbvClose

theorem combine_sub_add_reg_x_add_y_sub_y_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_y_pattern := by
  proveLegalValid with pbvClose

theorem combine_sub_add_reg_x_add_y_sub_x_valid : Puddle.CTree.Pattern.Valid sub_add_reg_x_add_y_sub_x_pattern := by
  proveLegalValid with pbvClose

theorem combine_sub_add_reg_negate_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern false) := by
  proveLegalValid with pbvClose

theorem combine_sub_add_reg_negate_x_first_valid : Puddle.CTree.Pattern.Valid (sub_add_reg_negate_pattern true) := by
  proveLegalValid with pbvClose

theorem combine_xor_of_and_with_same_reg_valid : Puddle.CTree.Pattern.Valid xor_of_and_with_same_reg_pattern := by
  proveLegalValid with pbvClose

theorem combine_trunc_of_zext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_zext) := by
  proveLegalValid with pbvClose

theorem combine_trunc_of_sext_valid : Puddle.CTree.Pattern.Valid (trunc_of_ext_pattern .g_sext) := by
  proveLegalValid with pbvClose

theorem combine_redundant_add_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .eq) := by
  proveLegalValid with pbvClose

theorem combine_redundant_add_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_add .ne) := by
  proveLegalValid with pbvClose

theorem combine_redundant_sub_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .eq) := by
  proveLegalValid with pbvClose

theorem combine_redundant_sub_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_sub .ne) := by
  proveLegalValid with pbvClose

theorem combine_redundant_xor_eq_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .eq) := by
  proveLegalValid with pbvClose

theorem combine_redundant_xor_ne_valid : Puddle.CTree.Pattern.Valid (redundant_binop_in_equality_pattern .g_xor .ne) := by
  proveLegalValid with pbvClose

theorem combine_combine_or_of_and_tt_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true true) := by
  proveLegalValid with pbvClose

theorem combine_combine_or_of_and_tf_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern true false) := by
  proveLegalValid with pbvClose

theorem combine_combine_or_of_and_ft_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false true) := by
  proveLegalValid with pbvClose

theorem combine_combine_or_of_and_ff_valid : Puddle.CTree.Pattern.Valid (combine_or_of_and_pattern false false) := by
  proveLegalValid with pbvClose

theorem combine_AMinusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusC_pattern := by
  proveLegalValid with pbvClose

theorem combine_zext_of_zext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_zext) := by
  proveLegalValid with pbvClose

theorem combine_sext_of_sext_valid : Puddle.CTree.Pattern.Valid (ext_of_ext_pattern .g_sext) := by
  proveLegalValid with pbvClose

-- the `icmp` predicate is abstracted
-- theorem combine_canonicalize_icmp_valid : Puddle.CTree.Pattern.Valid canonicalize_icmp_pattern := by
--   proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_bitreverse_shl_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_shl .g_lshr) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_bitreverse_lshr_valid : Puddle.CTree.Pattern.Valid (bitreverse_shift_pattern .g_lshr .g_shl) := by
  proveLegalValid with (pbvClose; all_goals sorry)

theorem combine_binop_same_val_and_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_and) := by
  proveLegalValid with pbvClose

theorem combine_binop_same_val_or_valid : Puddle.CTree.Pattern.Valid (binop_same_val_pattern .g_or) := by
  proveLegalValid with pbvClose

theorem combine_same_val_zero_sub_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_sub) := by
  proveLegalValid with pbvClose

theorem combine_same_val_zero_xor_valid : Puddle.CTree.Pattern.Valid (same_val_zero_pattern .g_xor) := by
  proveLegalValid with pbvClose

theorem combine_add_sub_reg_0_valid : Puddle.CTree.Pattern.Valid add_sub_reg_0_pattern := by
  proveLegalValid with pbvClose

theorem combine_add_sub_reg_1_valid : Puddle.CTree.Pattern.Valid add_sub_reg_1_pattern := by
  proveLegalValid with pbvClose

theorem combine_APlusBMinusCMinusB_valid : Puddle.CTree.Pattern.Valid APlusBMinusCMinusB_pattern := by
  proveLegalValid with pbvClose

theorem combine_AMinusBMinusCMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBMinusCMinusC_pattern := by
  proveLegalValid with pbvClose

theorem combine_AMinusBPlusCMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBPlusCMinusA_pattern := by
  proveLegalValid with pbvClose

theorem combine_AMinusBPlusBMinusC_valid : Puddle.CTree.Pattern.Valid AMinusBPlusBMinusC_pattern := by
  proveLegalValid with pbvClose

theorem combine_AMinusBMinusA_valid : Puddle.CTree.Pattern.Valid AMinusBMinusA_pattern := by
  proveLegalValid with pbvClose

theorem combine_APlusBMinusAPlusC_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern true) := by
  proveLegalValid with pbvClose

theorem combine_APlusBMinusCPlusA_valid : Puddle.CTree.Pattern.Valid (APlusBMinusAPlusC_pattern false) := by
  proveLegalValid with pbvClose

theorem combine_select_same_val_valid : Puddle.CTree.Pattern.Valid select_same_val_pattern := by
  proveLegalValid with pbvClose

theorem combine_select_ugt_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ugt .g_umax) := by
  proveLegalValid with pbvClose

theorem combine_select_uge_umax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .uge .g_umax) := by
  proveLegalValid with pbvClose

theorem combine_select_sgt_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sgt .g_smax) := by
  proveLegalValid with pbvClose

theorem combine_select_sge_smax_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sge .g_smax) := by
  proveLegalValid with pbvClose

theorem combine_select_ult_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ult .g_umin) := by
  proveLegalValid with pbvClose

theorem combine_select_ule_umin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .ule .g_umin) := by
  proveLegalValid with pbvClose

theorem combine_select_slt_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .slt .g_smin) := by
  proveLegalValid with pbvClose

theorem combine_select_sle_smin_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_to_iminmax_pattern info .sle .g_smin) := by
  proveLegalValid with pbvClose

theorem combine_zext_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_zext) := by
  proveLegalValid with pbvClose

theorem combine_trunc_of_select_valid (info : LegalizerInfo) : Puddle.CTree.Pattern.Valid (select_of_cast_pattern info .g_trunc) := by
  proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_sub_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_sub_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_sub true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_add_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_add_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_add true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_or_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_or_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_or true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_xor_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_select_into_xor_swapped_valid : Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_xor true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- the `icmp` predicate is abstracted (with `maxHeartbeats 0`; at the default it times out first)
-- theorem combine_redundant_and_select_icmp_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .icmp) := by
--   proveLegalValid with pbvClose

-- the `icmp` predicate is abstracted
-- theorem combine_redundant_and_valid : Puddle.CTree.Pattern.Valid redundant_and_pattern := by
--   proveLegalValid with pbvClose

-- the type group is a `TypeAttr`: the `Conforms` hypotheses of non-integer values are not decidable
-- theorem combine_funnel_shift_fshl_or_shl_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true true) := by
--   proveLegalValid with pbvClose

-- the type group is a `TypeAttr`: the `Conforms` hypotheses of non-integer values are not decidable
-- theorem combine_funnel_shift_shl_or_fshl_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshl .g_shl true false) := by
--   proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_funnel_shift_fshr_or_lshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false true) := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem combine_funnel_shift_lshr_or_fshr_valid :
    Puddle.CTree.Pattern.Valid (funnel_shift_or_shift_pattern .g_fshr .g_lshr false false) := by
  proveLegalValid with (pbvClose; all_goals sorry)

end Veir.Legalization.CTreeProofs.PBV
