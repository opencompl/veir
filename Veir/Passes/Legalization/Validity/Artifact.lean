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
import all Veir.Data.Refinement
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide

/-! CTree validity of the legalization artifact combines of `tryCombineInstruction`.

`combineAnyExtOfAnyExt` chooses the high bits of a matched `g_anyext` afresh
(`rechoosesMatchedChoice`). -/

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

theorem artifact_anyext_trunc_same_valid :
    Puddle.CTree.Pattern.Valid combineAnyExtOfTruncSame := by
  proveLegalValid using Data.LLVM.anyext_trunc_same

theorem artifact_anyext_trunc_narrower_valid : Puddle.CTree.Pattern.Valid
    (combineAnyExtOfTruncToCast .g_trunc (·.bitwidth > ·.bitwidth)) := by
  proveLegalValid using Data.LLVM.anyext_trunc_narrower

theorem artifact_anyext_trunc_wider_valid : Puddle.CTree.Pattern.Valid
    (combineAnyExtOfTruncToCast .g_anyext (·.bitwidth < ·.bitwidth)) := by
  proveLegalValid using Data.LLVM.anyext_trunc_wider

theorem artifact_trunc_trunc_valid : Puddle.CTree.Pattern.Valid combineTruncOfTrunc := by
  proveLegalValid using Data.LLVM.trunc_trunc

/-- The constant combines match the bits of the constant at the width of its attribute, which the
matcher ties to the width of the constant, so they are the constant's value. -/
theorem artifact_zext_trunc_constant_valid :
    Puddle.CTree.Pattern.Valid (combineExtOfTruncOfConstant false) := by
  proveLegalValid with
    simp only [GMIRConstantProperties.bits] at *
    apply Data.LLVM.zext_trunc_constant <;> simp_all

theorem artifact_sext_trunc_constant_valid :
    Puddle.CTree.Pattern.Valid (combineExtOfTruncOfConstant true) := by
  proveLegalValid with
    simp only [GMIRConstantProperties.bits] at *
    apply Data.LLVM.sext_trunc_constant <;> simp_all

/-- `g_unmerge_values` of `g_merge_values lo hi`, at the half width `k` the interpreter computes. -/
private theorem int_unmerge_merge {w k : Nat} (hk : k = w) (h : w + w = k + k) (lo hi : Data.LLVM.Int w) :
    RuntimeValue.int k (unmergeValues ((mergeValues lo hi).cast h)).fst ⊒ RuntimeValue.int w lo ∧
      RuntimeValue.int k (unmergeValues ((mergeValues lo hi).cast h)).snd ⊒ RuntimeValue.int w hi := by
  subst hk
  cases lo <;> cases hi <;>
    simp [RuntimeValue.isRefinedBy, mergeValues, unmergeValues, BitVec.setWidth_append_eq_right,
      BitVec.extractLsb'_append_eq_left, isRefinedBy_eq]

/-- The interpreter of `g_unmerge_values` halves the width `w + w` of its operand, which `simp`
cannot rewrite under the dependent result values, so this proof substitutes the merged value by
hand and closes the refinement with `int_unmerge_merge`. -/
theorem artifact_unmerge_merge_valid : Puddle.CTree.Pattern.Valid combineUnmergeOfMerge := by
  conv => arg 1; cbv
  simpPuddleValid
  intros
  clearVerified
  casesConformingValues
  all_goals casesIntegerTypes
  all_goals (try dsimp only at *)
  all_goals (try subst_vars)
  all_goals simp [ctree_semantics, Attribute.of, -Attribute.integerType_eq_of] at *
  all_goals casesExistsAnd
  all_goals subst_vars
  all_goals simp only [heq_eq_eq, dite_true] at *
  all_goals subst_vars
  rename_i _ v _ mem w _ _ _ _ _ lo hi hmerge
  obtain rfl := (Array.singleton_inj.mp (Prod.mk.inj (Interp.ok.inj hmerge)).1).symm
  have hk : (w + w) / 2 = w := by omega
  have key := int_unmerge_merge hk (by omega) lo (hi.cast rfl)
  simp only [List.toList_toArray,
    dite_eq_left_of_eq_true (show (w + w = (w + w) / 2 + (w + w) / 2) = True by simp; omega),
    Sim.bind_monadLift_right_iff, CTree.Sim.pure]
  simp only [Data.LLVM.Int.cast_self] at key ⊢
  refine ⟨⟨rfl, fun i hi' => ?_⟩, by simp, by simp [ControlFlowAction.optionIsRefinedBy]⟩
  match i, hi' with
  | 0, _ => exact key.1
  | 1, _ => exact key.2

/-- The truncation keeps the bit of the `g_icmp`, as the matcher excludes `i0`. -/
theorem artifact_zext_trunc_icmp_valid : Puddle.CTree.Pattern.Valid combineZExtOfTruncOfICmp := by
  proveLegalValid using Data.LLVM.zext_trunc_zext_bit

/-! ## Status of every artifact combine -/

@[legalization_status]
theorem artifact_0_status :
    Status Unproven (combineAnyExtOfTruncSame) :=
  .proven artifact_anyext_trunc_same_valid

@[legalization_status]
theorem artifact_1_status :
    Status Unproven (combineAnyExtOfTruncToCast .g_trunc (·.bitwidth > ·.bitwidth)) :=
  .proven artifact_anyext_trunc_narrower_valid

@[legalization_status]
theorem artifact_2_status :
    Status Unproven (combineAnyExtOfTruncToCast .g_anyext (·.bitwidth < ·.bitwidth)) :=
  .proven artifact_anyext_trunc_wider_valid

@[legalization_status]
theorem artifact_3_status :
    Status Unproven (combineAnyExtOfAnyExt) :=
  .unproven .rechoosesMatchedChoice

@[legalization_status]
theorem artifact_4_status :
    Status Unproven (combineZExtOfTruncOfICmp) :=
  .proven artifact_zext_trunc_icmp_valid

@[legalization_status]
theorem artifact_5_status :
    Status Unproven (combineExtOfTruncOfConstant false) :=
  .proven artifact_zext_trunc_constant_valid

@[legalization_status]
theorem artifact_6_status :
    Status Unproven (combineExtOfTruncOfConstant true) :=
  .proven artifact_sext_trunc_constant_valid

@[legalization_status]
theorem artifact_7_status :
    Status Unproven (combineTruncOfTrunc) :=
  .proven artifact_trunc_trunc_valid

@[legalization_status]
theorem artifact_8_status :
    Status Unproven (combineUnmergeOfMerge) :=
  .proven artifact_unmerge_merge_valid

end Veir.Legalization.CTreeProofs
