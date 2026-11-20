module

import all Veir.Passes.Legalization.Validity.Common
import all Veir.Passes.Legalization.LegalizerHelper
import all Veir.Passes.Legalization.LegalizationArtifactCombiner
import all Veir.Passes.Legalization.RISCV64LegalizerInfo
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

/-- `ofInt` of a difference, as `BitVec.ofInt_add` for a sum. -/
theorem ofInt_sub' {n : Nat} (x y : _root_.Int) :
    BitVec.ofInt n (x - y) = BitVec.ofInt n x - BitVec.ofInt n y := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- Rewrite the width constants that a rule builds as integers, such as `BitVec.ofInt n (↑w - 1)`,
to `BitVec.ofNat n w - 1`, a width placed in a value, which `pbv_decide` translates. -/
local macro "widthNorm" : tactic => `(tactic|
  (try simp only [ofInt_sub', BitVec.ofInt_natCast, BitVec.ofInt_ofNat] at *))

@[proof_manual]
theorem custom_urem_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_remuw) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_urem_status :
    Status Unproven (customLegalizeWordBinary .g_remuw) :=
  .proven custom_urem_valid

@[proof_manual]
theorem custom_ctlz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_clzw) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_ctlz_status :
    Status Unproven (customLegalizeWordUnary .g_clzw) :=
  .proven custom_ctlz_valid

@[proof_manual]
theorem custom_cttz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_ctzw) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_cttz_status :
    Status Unproven (customLegalizeWordUnary .g_ctzw) :=
  .proven custom_cttz_valid

@[proof_pbv]
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
@[proof_pbv]
theorem custom_uaddsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_uaddsat false true) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_uaddsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_uaddsat false true) :=
  .proven custom_uaddsat_valid

-- Up to 64 bits only: the matcher leaves the widths unbounded, so the side goals `w ≤ 64` are assumed.
@[proof_pbv]
theorem custom_usubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_usubsat false false) := by
  proveLegalValid with veir_pbv_decide 64

@[legalization_status]
theorem custom_usubsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_usubsat false false) :=
  .proven custom_usubsat_valid

@[proof_pbv]
theorem custom_saddsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_saddsat true true) := by
  proveLegalValid with (all_goals widthNorm; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem custom_saddsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_saddsat true true) :=
  .proven custom_saddsat_valid

@[proof_pbv]
theorem custom_ssubsat_valid :
    Puddle.CTree.Pattern.Valid (lowerAddSubSatToAddoSubo .g_ssubsat true false) := by
  proveLegalValid with (all_goals widthNorm; all_goals (veir_pbv_decide 64 (bv_decide := false)); all_goals bv_decide (config := { timeout := 300 }))

@[legalization_status]
theorem custom_ssubsat_status :
    Status Unproven (lowerAddSubSatToAddoSubo .g_ssubsat true false) :=
  .proven custom_ssubsat_valid

end Veir.Legalization.CTreeProofs.PBV
