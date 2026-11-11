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

/-! CTree validity of the legalization artifact combines of `tryCombineInstruction`.

The constant combines read the constant's bits at the width of its attribute, which the matcher
does not tie to the width of its result, hence `needsTypedMatch`. -/

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
  .unproven .notYetProven

@[legalization_status]
theorem artifact_4_status :
    Status Unproven (combineZExtOfTruncOfICmp) :=
  .unproven .notYetProven

@[legalization_status]
theorem artifact_5_status :
    Status Unproven (combineExtOfTruncOfConstant false) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem artifact_6_status :
    Status Unproven (combineExtOfTruncOfConstant true) :=
  .unproven .needsTypedMatch

@[legalization_status]
theorem artifact_7_status :
    Status Unproven (combineTruncOfTrunc) :=
  .proven artifact_trunc_trunc_valid

@[legalization_status]
theorem artifact_8_status :
    Status Unproven (combineUnmergeOfMerge) :=
  .unproven .notYetProven

end Veir.Legalization.CTreeProofs
