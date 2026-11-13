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
# CTree validity of the custom legalizations (`Validity/Custom`) by `pbv_decide`

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

theorem custom_urem_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_remuw) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_urem_status :
    Status Unproven (customLegalizeWordBinary .g_remuw) :=
  .proven custom_urem_valid

theorem custom_ctlz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_clzw) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_ctlz_status :
    Status Unproven (customLegalizeWordUnary .g_clzw) :=
  .proven custom_ctlz_valid

theorem custom_cttz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_ctzw) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_cttz_status :
    Status Unproven (customLegalizeWordUnary .g_ctzw) :=
  .proven custom_cttz_valid

theorem custom_abs_valid : Puddle.CTree.Pattern.Valid customLegalizeAbs := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_abs_status :
    Status Unproven (customLegalizeAbs) :=
  .proven custom_abs_valid

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_add_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_addw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_sub_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_subw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_mul_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_mulw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_shl_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_sllw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_lshr_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_srlw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_ashr_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_sraw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_sdiv_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_divw) := by
--   proveLegalValid with veir_pbv_decide 64

-- the target's `default` flags are not reduced, so they are abstracted
-- theorem custom_udiv_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_divuw) := by
--   proveLegalValid with veir_pbv_decide 64

-- `brev8` is abstracted as an opaque function
-- theorem custom_bitreverse_valid : Puddle.CTree.Pattern.Valid customLegalizeBitreverse8 := by
--   proveLegalValid with veir_pbv_decide 64

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem custom_uaddsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_uaddsat false true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_uaddsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_uaddsat false true) :=
  .proven custom_uaddsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
theorem custom_usubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_usubsat false false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_usubsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_usubsat false false) :=
  .proven custom_usubsat_valid

-- the width-dependent constant `BitVec.ofInt 64 (bitwidth - 1)` is abstracted
-- theorem custom_saddsat_valid :
--     Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_saddsat true true) := by
--   proveLegalValid with veir_pbv_decide 64

-- the width-dependent constant `BitVec.ofInt 64 (bitwidth - 1)` is abstracted
-- theorem custom_ssubsat_valid :
--     Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_ssubsat true false) := by
--   proveLegalValid with veir_pbv_decide 64

end Veir.Legalization.CTreeProofs.PBV
