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
import all Veir.Data.Refinement
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.PBVDecide

/-!
# CTree validity of the legalization artifact combines (`Validity/Artifact`) by `pbv_decide`

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

-- the `IntegerType` equalities are not split into width equations
-- theorem artifact_anyext_trunc_same_valid :
--     Puddle.CTree.Pattern.Valid combineAnyExtOfTruncSame := by
--   proveLegalValid with pbvClose

-- the goal is existential in the `anyext` choice, which `pbv_decide` does not decide
-- theorem artifact_anyext_trunc_narrower_valid : Puddle.CTree.Pattern.Valid
--     (combineAnyExtOfTruncToCast .g_trunc (·.bitwidth > ·.bitwidth)) := by
--   proveLegalValid with pbvClose

-- the goal is existential in the `anyext` choice, which `pbv_decide` does not decide
-- theorem artifact_anyext_trunc_wider_valid : Puddle.CTree.Pattern.Valid
--     (combineAnyExtOfTruncToCast .g_anyext (·.bitwidth < ·.bitwidth)) := by
--   proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem artifact_trunc_trunc_valid : Puddle.CTree.Pattern.Valid combineTruncOfTrunc := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
theorem artifact_zext_trunc_constant_valid :
    Puddle.CTree.Pattern.Valid (combineExtOfTruncOfConstant false) := by
  proveLegalValid with
    -- trace_state
    simp only [GMIRConstantProperties.bits] at *
    veir_bv_normalize
    pbv_decide 64

-- the matched constant's properties (`bits`, `isZero`, ...) stay opaque
-- theorem artifact_sext_trunc_constant_valid :
--     Puddle.CTree.Pattern.Valid (combineExtOfTruncOfConstant true) := by
--   proveLegalValid with pbvClose

-- the `proveLegalValid` pipeline fails before `pbv_decide` runs
-- theorem artifact_unmerge_merge_valid : Puddle.CTree.Pattern.Valid combineUnmergeOfMerge := by
--   proveLegalValid with pbvClose

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem artifact_zext_trunc_icmp_valid : Puddle.CTree.Pattern.Valid combineZExtOfTruncOfICmp := by
  proveLegalValid with (pbvClose; all_goals sorry)

-- rechooses the matched `anyext` choice (`.rechoosesMatchedChoice`); the goal is existential in it
-- theorem artifact_anyext_anyext_valid :
--     Puddle.CTree.Pattern.Valid combineAnyExtOfAnyExt := by
--   proveLegalValid with pbvClose

end Veir.Legalization.CTreeProofs.PBV
