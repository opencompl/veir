module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
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
meta import Veir.Meta.ProofKind

/-!
# CTree validity of the legalization artifact combines (`Validity/Artifact`) by `pbv_decide`

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

-- the `IntegerType` equalities are not split into width equations
-- theorem artifact_anyext_trunc_same_valid :
--     Puddle.CTree.Pattern.Valid combineAnyExtOfTruncSame := by
--   proveLegalValid with veir_pbv_decide 64 (blastWidth := 64)

-- the goal is existential in the `anyext` choice, which `pbv_decide` does not decide
-- theorem artifact_anyext_trunc_narrower_valid : Puddle.CTree.Pattern.Valid
--     (combineAnyExtOfTruncToCast .g_trunc (·.bitwidth > ·.bitwidth)) := by
--   proveLegalValid with veir_pbv_decide 64 (blastWidth := 64)

-- the goal is existential in the `anyext` choice, which `pbv_decide` does not decide
-- theorem artifact_anyext_trunc_wider_valid : Puddle.CTree.Pattern.Valid
--     (combineAnyExtOfTruncToCast .g_anyext (·.bitwidth < ·.bitwidth)) := by
--   proveLegalValid with veir_pbv_decide 64 (blastWidth := 64)

@[proof_pbv]
theorem artifact_trunc_trunc_valid : Puddle.CTree.Pattern.Valid combineTruncOfTrunc := by
  proveLegalValid with (veir_pbv_decide 64)

@[legalization_status]
theorem artifact_7_status :
    Status Unproven (combineTruncOfTrunc) :=
  .proven artifact_trunc_trunc_valid

-- spurious counterexample: the constant's value is abstracted from its width
-- theorem artifact_zext_trunc_constant_valid :
--     Puddle.CTree.Pattern.Valid (combineExtOfTruncOfConstant false) := by
--   proveLegalValid with
--     -- trace_state
--     simp only [GMIRConstantProperties.bits] at *
--     veir_pbv_decide 64

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem artifact_sext_trunc_constant_valid :
--     Puddle.CTree.Pattern.Valid (combineExtOfTruncOfConstant true) := by
--   proveLegalValid with veir_pbv_decide 64 (blastWidth := 64)

-- the `proveLegalValid` pipeline fails before `pbv_decide` runs
-- theorem artifact_unmerge_merge_valid : Puddle.CTree.Pattern.Valid combineUnmergeOfMerge := by
--   proveLegalValid with veir_pbv_decide 64 (blastWidth := 64)

@[proof_pbv]
theorem artifact_zext_trunc_icmp_valid : Puddle.CTree.Pattern.Valid combineZExtOfTruncOfICmp := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem artifact_4_status :
    Status Unproven (combineZExtOfTruncOfICmp) :=
  .proven artifact_zext_trunc_icmp_valid

-- rechooses the matched `anyext` choice (`.rechoosesMatchedChoice`); the goal is existential in it
-- theorem artifact_anyext_anyext_valid :
--     Puddle.CTree.Pattern.Valid combineAnyExtOfAnyExt := by
--   proveLegalValid with veir_pbv_decide 64 (blastWidth := 64)

end Veir.Legalization.CTreeProofs.PBV
