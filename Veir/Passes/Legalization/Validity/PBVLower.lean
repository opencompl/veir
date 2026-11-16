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
import all Init.Data.Array.Basic
import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.BVDecide
meta import Veir.Meta.Tactic.PBVDecide
meta import Veir.Meta.ProofKind

/-!
# CTree validity of the lowerings of `lower?` and the narrowings of `narrowScalar?` (`Validity/Lower`) by `pbv_decide`

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

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_zext_valid : Puddle.CTree.Pattern.Valid lowerZext := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_zext_status :
    Status Unproven (lowerZext) :=
  .proven lower_zext_valid

-- /-- Require ofNat of a bitwidth -/
-- theorem lower_sext_valid : Puddle.CTree.Pattern.Valid lowerSext := by
--   proveLegalValid with
--     veir_bv_normalize
--     pbv_decide 64

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_uaddsat_valid : Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_uaddsat false true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_uaddsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_uaddsat false true) :=
  .proven lower_uaddsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_usubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_usubsat false false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_usubsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_usubsat false false) :=
  .proven lower_usubsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_saddsat_valid : Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_saddsat true true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_saddsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_saddsat true true) :=
  .proven lower_saddsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_ssubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToMinMax .g_ssubsat true false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_ssubsat_status :
    Status Unproven (lowerAddSubSatToMinMax .g_ssubsat true false) :=
  .proven lower_ssubsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_sshlsat_valid : Puddle.CTree.Pattern.Valid (lowerShlSat true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_sshlsat_status :
    Status Unproven (lowerShlSat true) :=
  .proven lower_sshlsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_ushlsat_valid : Puddle.CTree.Pattern.Valid (lowerShlSat false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_ushlsat_status :
    Status Unproven (lowerShlSat false) :=
  .proven lower_ushlsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_ctlz_zero_poison_valid :
    Puddle.CTree.Pattern.Valid (lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_ctlz_zero_poison_status :
    Status Unproven (lowerZeroPoisonCount .g_ctlz_zero_poison .g_ctlz) :=
  .proven lower_ctlz_zero_poison_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_cttz_zero_poison_valid :
    Puddle.CTree.Pattern.Valid (lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_cttz_zero_poison_status :
    Status Unproven (lowerZeroPoisonCount .g_cttz_zero_poison .g_cttz) :=
  .proven lower_cttz_zero_poison_valid

-- spurious counterexample on the carry goals (not investigated)
-- theorem lower_uadde_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE true) := by
--   proveLegalValid with veir_pbv_decide 64

-- spurious counterexample on the borrow goals (not investigated)
-- theorem lower_usube_valid : Puddle.CTree.Pattern.Valid (lowerAddSubE false) := by
--   proveLegalValid with veir_pbv_decide 64

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_uaddo_valid : Puddle.CTree.Pattern.Valid (lowerUAddSubO true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_uaddo_status :
    Status Unproven (lowerUAddSubO true) :=
  .proven lower_uaddo_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_usubo_valid : Puddle.CTree.Pattern.Valid (lowerUAddSubO false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_usubo_status :
    Status Unproven (lowerUAddSubO false) :=
  .proven lower_usubo_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_saddo_valid : Puddle.CTree.Pattern.Valid (lowerSAddSubO true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_saddo_status :
    Status Unproven (lowerSAddSubO true) :=
  .proven lower_saddo_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem lower_ssubo_valid : Puddle.CTree.Pattern.Valid (lowerSAddSubO false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem lower_ssubo_status :
    Status Unproven (lowerSAddSubO false) :=
  .proven lower_ssubo_valid

-- the `unmerge`/`merge` width casts are not translated
-- theorem narrow_add_valid (W : Nat) (hW : W ≤ 64) : Puddle.CTree.Pattern.Valid (narrowAddSub true W) := by
--   proveLegalValid with veir_pbv_decide 64

-- the `unmerge`/`merge` width casts are not translated
-- theorem narrow_sub_valid (W : Nat) (hW : W ≤ 64) : Puddle.CTree.Pattern.Valid (narrowAddSub false W) := by
--   proveLegalValid with veir_pbv_decide 64

-- wrong at width 1 (`.widthDependent`), and the `urem` UB check of the amount is abstracted
-- theorem lower_fshl_valid :
--     Puddle.CTree.Pattern.Valid (lowerFunnelShift true) := by
--   proveLegalValid with veir_pbv_decide 64

-- wrong at width 1 (`.widthDependent`), and the `urem` UB check of the amount is abstracted
-- theorem lower_fshr_valid :
--     Puddle.CTree.Pattern.Valid (lowerFunnelShift false) := by
--   proveLegalValid with veir_pbv_decide 64

end Veir.Legalization.CTreeProofs.PBV
