module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
import all Veir.Passes.Legalization.CombinerHelper
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.GMIR.Properties
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.Semantics
import all Veir.Dialects.GMIR_RISCV.OpInfo
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Int.Bitblast
import all Veir.Passes.Legalization.Validity.PBVNormalize
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.PBVDecide

/-!
# CTree validity of the gMIR combines that match constants (`Validity/CombineConstant`) by `pbv_decide`

Each rule is proven by `proveLegalValid with veir_pbv_decide` alone, without `sorry`: the matchers
bound every integer width by 64, which discharges the side goals `w ≤ 64` of `pbv_decide`. The rules `veir_pbv_decide` does not prove are commented out, with the reason it
fails.
-/
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

/-- The predicates the combines test on a matched constant, read at the width of its result. -/
local macro "simpConstantPreds" : tactic => `(tactic|
  simp only [GMIRConstantProperties.bits, GMIRConstantProperties.isZero, GMIRConstantProperties.isOne,
    GMIRConstantProperties.isAllOnes, GMIRConstantProperties.isMinSigned, GMIRConstantProperties.neg,
    GMIRConstantProperties.isOffsetOf, GMIRConstantProperties.log2?, GMIRConstantProperties.ulog2?,
    GMIRConstantProperties.slog2?, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.or_eq_true] at *)

/-- As in `Validity/CombineConstant`. Normalize the goals of a combine that matches constants: split each constant's properties and
substitute its type, which `matchConstant` equates to the result type, so that each constant is
`BitVec.ofInt w v` at its result width `w`. -/
local macro "normalizeConstants" : tactic => `(tactic| (
  all_goals intros
  all_goals (casesLocalsOf GMIRConstantProperties IntegerAttr)
  all_goals casesIntegerTypes
  all_goals (try simp only [IntegerType.mk.injEq] at *)
  all_goals (try casesExistsAnd)
  all_goals (try subst_vars)
  all_goals (try simpConstantPreds)))

@[combine_valid]
theorem combine_right_identity_zero_sub_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_sub) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_sub_status :
    Status Unproven (right_identity_zero_pattern .g_sub) :=
  .proven (combine_right_identity_zero_sub_valid)

@[combine_valid]
theorem combine_right_identity_zero_add_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_add) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_add_status :
    Status Unproven (right_identity_zero_pattern .g_add) :=
  .proven (combine_right_identity_zero_add_valid)

@[combine_valid]
theorem combine_right_identity_zero_or_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_or) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_or_status :
    Status Unproven (right_identity_zero_pattern .g_or) :=
  .proven (combine_right_identity_zero_or_valid)

@[combine_valid]
theorem combine_right_identity_zero_xor_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_xor) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_xor_status :
    Status Unproven (right_identity_zero_pattern .g_xor) :=
  .proven (combine_right_identity_zero_xor_valid)

@[combine_valid]
theorem combine_right_identity_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_shl) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_shl_status :
    Status Unproven (right_identity_zero_pattern .g_shl) :=
  .proven (combine_right_identity_zero_shl_valid)

@[combine_valid]
theorem combine_right_identity_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_ashr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_ashr_status :
    Status Unproven (right_identity_zero_pattern .g_ashr) :=
  .proven (combine_right_identity_zero_ashr_valid)

@[combine_valid]
theorem combine_right_identity_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (right_identity_zero_pattern .g_lshr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_right_identity_zero_lshr_status :
    Status Unproven (right_identity_zero_pattern .g_lshr) :=
  .proven (combine_right_identity_zero_lshr_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_right_identity_one_int_valid :
--     Puddle.CTree.Pattern.Valid (right_identity_one_int_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_binop_right_to_zero_valid :
    Puddle.CTree.Pattern.Valid (binop_right_to_zero_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_right_to_zero_status :
    Status Unproven (binop_right_to_zero_pattern) :=
  .proven (combine_binop_right_to_zero_valid)

@[combine_valid]
theorem combine_binop_left_to_zero_shl_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_shl) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_shl_status :
    Status Unproven (binop_left_to_zero_pattern .g_shl) :=
  .proven (combine_binop_left_to_zero_shl_valid)

@[combine_valid]
theorem combine_binop_left_to_zero_lshr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_lshr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_lshr_status :
    Status Unproven (binop_left_to_zero_pattern .g_lshr) :=
  .proven (combine_binop_left_to_zero_lshr_valid)

@[combine_valid]
theorem combine_binop_left_to_zero_ashr_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_ashr) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_ashr_status :
    Status Unproven (binop_left_to_zero_pattern .g_ashr) :=
  .proven (combine_binop_left_to_zero_ashr_valid)

@[combine_valid]
theorem combine_binop_left_to_zero_mul_valid :
    Puddle.CTree.Pattern.Valid (binop_left_to_zero_pattern .g_mul) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_binop_left_to_zero_mul_status :
    Status Unproven (binop_left_to_zero_pattern .g_mul) :=
  .proven (combine_binop_left_to_zero_mul_valid)

@[combine_valid]
theorem combine_sub_minus_one_valid :
    Puddle.CTree.Pattern.Valid (sub_minus_one_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_minus_one_status :
    Status Unproven (sub_minus_one_pattern) :=
  .proven (combine_sub_minus_one_valid)

@[combine_valid]
theorem combine_ZeroMinusAPlusB_valid :
    Puddle.CTree.Pattern.Valid (ZeroMinusAPlusB_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_ZeroMinusAPlusB_status :
    Status Unproven (ZeroMinusAPlusB_pattern) :=
  .proven (combine_ZeroMinusAPlusB_valid)

@[combine_valid]
theorem combine_APlusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (APlusZeroMinusB_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusZeroMinusB_status :
    Status Unproven (APlusZeroMinusB_pattern) :=
  .proven (combine_APlusZeroMinusB_valid)

@[combine_valid]
theorem combine_AMinusZeroMinusB_valid :
    Puddle.CTree.Pattern.Valid (AMinusZeroMinusB_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusZeroMinusB_status :
    Status Unproven (AMinusZeroMinusB_pattern) :=
  .proven (combine_AMinusZeroMinusB_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_one_from_sub_valid :
--     Puddle.CTree.Pattern.Valid (sub_one_from_sub_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_APlusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (APlusC1MinusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_APlusC1MinusC2_status :
    Status Unproven (APlusC1MinusC2_pattern) :=
  .proven (combine_APlusC1MinusC2_valid)

@[combine_valid]
theorem combine_C2MinusAPlusC1_valid :
    Puddle.CTree.Pattern.Valid (C2MinusAPlusC1_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_C2MinusAPlusC1_status :
    Status Unproven (C2MinusAPlusC1_pattern) :=
  .proven (combine_C2MinusAPlusC1_valid)

@[combine_valid]
theorem combine_AMinusC1MinusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1MinusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusC1MinusC2_status :
    Status Unproven (AMinusC1MinusC2_pattern) :=
  .proven (combine_AMinusC1MinusC2_valid)

@[combine_valid]
theorem combine_C1MinusAMinusC2_valid :
    Puddle.CTree.Pattern.Valid (C1MinusAMinusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_C1MinusAMinusC2_status :
    Status Unproven (C1MinusAMinusC2_pattern) :=
  .proven (combine_C1MinusAMinusC2_valid)

@[combine_valid]
theorem combine_AMinusC1PlusC2_valid :
    Puddle.CTree.Pattern.Valid (AMinusC1PlusC2_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_AMinusC1PlusC2_status :
    Status Unproven (AMinusC1PlusC2_pattern) :=
  .proven (combine_AMinusC1PlusC2_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sub_of_mul_const_valid :
--     Puddle.CTree.Pattern.Valid (sub_of_mul_const_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_by_neg_one_valid :
--     Puddle.CTree.Pattern.Valid (mul_by_neg_one_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mulo_by_2_valid :
--     Puddle.CTree.Pattern.Valid (mulo_by_2_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_NotAPlusNegOne_valid :
    Puddle.CTree.Pattern.Valid (NotAPlusNegOne_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_NotAPlusNegOne_status :
    Status Unproven (NotAPlusNegOne_pattern) :=
  .proven (combine_NotAPlusNegOne_valid)

@[combine_valid]
theorem combine_add_shift_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern false) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_add_shift_status :
    Status Unproven (add_shift_pattern false) :=
  .proven (combine_add_shift_valid)

@[combine_valid]
theorem combine_add_shift_swapped_valid :
    Puddle.CTree.Pattern.Valid (add_shift_pattern true) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_add_shift_swapped_status :
    Status Unproven (add_shift_pattern true) :=
  .proven (combine_add_shift_swapped_valid)

@[combine_valid]
theorem combine_or_and_xor_to_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_or .g_and) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_or_or_and_status :
    Status Unproven (or_and_xor_to_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_or_or_and_valid)

@[combine_valid]
theorem combine_or_and_xor_to_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_or_pattern .g_and .g_or) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_or_and_or_status :
    Status Unproven (or_and_xor_to_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_or_and_or_valid)

@[combine_valid]
theorem combine_or_and_xor_to_xor_or_or_and_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_or .g_and) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_or_and_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_or .g_and) :=
  .proven (combine_or_and_xor_to_xor_or_or_and_valid)

@[combine_valid]
theorem combine_or_and_xor_to_xor_or_and_or_valid :
    Puddle.CTree.Pattern.Valid (or_and_xor_to_xor_or_pattern .g_and .g_or) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_or_and_xor_to_xor_or_and_or_status :
    Status Unproven (or_and_xor_to_xor_or_pattern .g_and .g_or) :=
  .proven (combine_or_and_xor_to_xor_or_and_or_valid)

@[combine_valid]
theorem combine_simplify_neg_smax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smax .g_smin) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_smax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smax .g_smin) :=
  .proven (combine_simplify_neg_smax_valid)

@[combine_valid]
theorem combine_simplify_neg_umax_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umax .g_umin) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_umax_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umax .g_umin) :=
  .proven (combine_simplify_neg_umax_valid)

@[combine_valid]
theorem combine_simplify_neg_smin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_smin .g_smax) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_smin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_smin .g_smax) :=
  .proven (combine_simplify_neg_smin_valid)

@[combine_valid]
theorem combine_simplify_neg_umin_valid :
    Puddle.CTree.Pattern.Valid (simplify_neg_minmax_pattern .g_umin .g_umax) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_simplify_neg_umin_status :
    Status Unproven (simplify_neg_minmax_pattern .g_umin .g_umax) :=
  .proven (combine_simplify_neg_umin_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_eq_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .eq .ne) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ne_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ne .eq) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ugt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ugt .ule) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_uge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .uge .ult) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ult_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ult .uge) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_ule_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .ule .ugt) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sgt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sgt .sle) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sge_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sge .slt) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_slt_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .slt .sge) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_not_cmp_fold_sle_valid :
--     Puddle.CTree.Pattern.Valid (not_cmp_fold_pattern .sle .sgt) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_double_icmp_zero_and_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_and .eq) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_double_icmp_zero_and_status :
    Status Unproven (double_icmp_zero_pattern .g_and .eq) :=
  .proven (combine_double_icmp_zero_and_valid)

@[combine_valid]
theorem combine_double_icmp_zero_or_valid :
    Puddle.CTree.Pattern.Valid (double_icmp_zero_pattern .g_or .ne) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_double_icmp_zero_or_status :
    Status Unproven (double_icmp_zero_pattern .g_or .ne) :=
  .proven (combine_double_icmp_zero_or_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_udiv_by_pow2_valid :
--     Puddle.CTree.Pattern.Valid (udiv_by_pow2_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern false) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_exact_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_exact_by_pow2_pattern true) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_pos_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern false) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_sdiv_by_pow2_neg_valid :
--     Puddle.CTree.Pattern.Valid (sdiv_by_pow2_pattern true) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_mul_to_shl_valid :
--     Puddle.CTree.Pattern.Valid (mul_to_shl_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_urem_pow2_to_mask_valid :
--     Puddle.CTree.Pattern.Valid (urem_pow2_to_mask_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_constant_fold_add_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_add (fun a b => a + b)) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_add_status :
    Status Unproven (constant_fold_binop_pattern .g_add (fun a b => a + b)) :=
  .proven (combine_constant_fold_add_valid)

@[combine_valid]
theorem combine_constant_fold_sub_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_sub ((· - ·))) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_sub_status :
    Status Unproven (constant_fold_binop_pattern .g_sub ((· - ·))) :=
  .proven (combine_constant_fold_sub_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_constant_fold_mul_valid :
--     Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_mul ((· * ·))) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_constant_fold_smin_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smin (min)) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_smin_status :
    Status Unproven (constant_fold_binop_pattern .g_smin (min)) :=
  .proven (combine_constant_fold_smin_valid)

@[combine_valid]
theorem combine_constant_fold_smax_valid :
    Puddle.CTree.Pattern.Valid (constant_fold_binop_pattern .g_smax (max)) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_constant_fold_smax_status :
    Status Unproven (constant_fold_binop_pattern .g_smax (max)) :=
  .proven (combine_constant_fold_smax_valid)

@[combine_valid]
theorem combine_select_constant_cmp_nonzero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern true) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_constant_cmp_nonzero_status :
    Status Unproven (select_constant_cmp_pattern true) :=
  .proven (combine_select_constant_cmp_nonzero_valid)

@[combine_valid]
theorem combine_select_constant_cmp_zero_valid :
    Puddle.CTree.Pattern.Valid (select_constant_cmp_pattern false) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_constant_cmp_zero_status :
    Status Unproven (select_constant_cmp_pattern false) :=
  .proven (combine_select_constant_cmp_zero_valid)

@[combine_valid]
theorem combine_sub_to_add_valid (info : LegalizerInfo) :
    Puddle.CTree.Pattern.Valid (sub_to_add_pattern info) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_sub_to_add_status (info : LegalizerInfo) :
    Status Unproven (sub_to_add_pattern info) :=
  .proven (combine_sub_to_add_valid info)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_icmp_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .icmp .constant) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_icmp_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .icmp) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_redundant_and_select_constant_constant_valid :
--     Puddle.CTree.Pattern.Valid (redundant_and_select_pattern .constant .constant) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_select_into_shl_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_shl_status :
    Status Unproven (select_into_binop_pattern .g_shl false) :=
  .proven (combine_select_into_shl_valid)

@[combine_valid]
theorem combine_select_into_shl_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_shl true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_shl_swapped_status :
    Status Unproven (select_into_binop_pattern .g_shl true) :=
  .proven (combine_select_into_shl_swapped_valid)

@[combine_valid]
theorem combine_select_into_lshr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_lshr_status :
    Status Unproven (select_into_binop_pattern .g_lshr false) :=
  .proven (combine_select_into_lshr_valid)

@[combine_valid]
theorem combine_select_into_lshr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_lshr true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_lshr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_lshr true) :=
  .proven (combine_select_into_lshr_swapped_valid)

@[combine_valid]
theorem combine_select_into_ashr_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr false) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_ashr_status :
    Status Unproven (select_into_binop_pattern .g_ashr false) :=
  .proven (combine_select_into_ashr_valid)

@[combine_valid]
theorem combine_select_into_ashr_swapped_valid :
    Puddle.CTree.Pattern.Valid (select_into_binop_pattern .g_ashr true) := by
  proveLegalValid with (veir_pbv_decide 64 (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_into_ashr_swapped_status :
    Status Unproven (select_into_binop_pattern .g_ashr true) :=
  .proven (combine_select_into_ashr_swapped_valid)

@[combine_valid]
theorem combine_select_one_zero_valid :
    Puddle.CTree.Pattern.Valid (select_one_zero_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_one_zero_status :
    Status Unproven (select_one_zero_pattern) :=
  .proven (combine_select_one_zero_valid)

@[combine_valid]
theorem combine_select_allOnes_zero_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_zero_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_allOnes_zero_status :
    Status Unproven (select_allOnes_zero_pattern) :=
  .proven (combine_select_allOnes_zero_valid)

@[combine_valid]
theorem combine_select_zero_one_valid :
    Puddle.CTree.Pattern.Valid (select_zero_one_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_zero_one_status :
    Status Unproven (select_zero_one_pattern) :=
  .proven (combine_select_zero_one_valid)

@[combine_valid]
theorem combine_select_zero_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_zero_allOnes_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_zero_allOnes_status :
    Status Unproven (select_zero_allOnes_pattern) :=
  .proven (combine_select_zero_allOnes_valid)

@[combine_valid]
theorem combine_select_succ_valid :
    Puddle.CTree.Pattern.Valid (select_succ_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_succ_status :
    Status Unproven (select_succ_pattern) :=
  .proven (combine_select_succ_valid)

@[combine_valid]
theorem combine_select_pred_valid :
    Puddle.CTree.Pattern.Valid (select_pred_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_pred_status :
    Status Unproven (select_pred_pattern) :=
  .proven (combine_select_pred_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_pow2_zero_valid :
--     Puddle.CTree.Pattern.Valid (select_pow2_zero_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_select_zero_pow2_valid :
--     Puddle.CTree.Pattern.Valid (select_zero_pow2_pattern) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

@[combine_valid]
theorem combine_select_allOnes_const_valid :
    Puddle.CTree.Pattern.Valid (select_allOnes_const_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_allOnes_const_status :
    Status Unproven (select_allOnes_const_pattern) :=
  .proven (combine_select_allOnes_const_valid)

@[combine_valid]
theorem combine_select_const_allOnes_valid :
    Puddle.CTree.Pattern.Valid (select_const_allOnes_pattern) := by
  proveLegalValid with (normalizeConstants; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem combine_select_const_allOnes_status :
    Status Unproven (select_const_allOnes_pattern) :=
  .proven (combine_select_const_allOnes_valid)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_right_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshr true) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem combine_funnel_shift_left_zero_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_zero_pattern .g_fshl false) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_l_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshl) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

-- spurious counterexample: the overshift amount's hypotheses are abstracted
-- theorem combine_funnel_shift_overshift_r_valid :
--     Puddle.CTree.Pattern.Valid (funnel_shift_overshift_pattern .g_fshr) := by
--   proveLegalValid with (veir_pbv_decide 64 (blastWidth := 64) (bv_decide := false); all_goals bv_decide (config := { timeout := 300 }))

end Veir.Legalization.CTreeProofs.PBV
