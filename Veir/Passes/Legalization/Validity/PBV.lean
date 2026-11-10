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
# CTree validity of the legalization rules by `pbv_decide`

The rules of `Validity/{Widen,Lower,Custom,Artifact}` that have a CTree validity proof, proven
again by bitblasting the normalized value goals with `pbv_decide 64` instead of the hand-written
local correctness lemmas.

`pbv_decide 64` proves a goal at every width up to 64 bits. The widenings take the bound on their
target width `W`, which bounds every width of the widened type group. Widths the matcher leaves
unbounded (those of the lowerings, and of the other type groups of a widening) give side goals
`w ≤ 128` that `grind` cannot close; `pbvClose` assumes them with `sorry`, so a theorem that uses
`sorry` here is proven up to 64 bits only.
-/
set_option Elab.async false
namespace Veir.Legalization.CTreeProofs.PBV

open Puddle
open Puddle.CTree
open _root_.CTree

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

attribute [local ctree_semantics]
  OperationResult.isRefinedBy Veir.interpretOp' Veir.CTree.interpretOp' CTree.CanInterpretTo
  GMIR.interpretOp' GMIR.interpretOpCTree GMIR_RISCV.interpretOp'

attribute [local simp] GMIR.isTerminator GMIR.getEffects GMIR_RISCV.base

attribute [local implicit_reducible] TypeAttr

/-- Close a normalized value goal by `pbv_decide 64`, assuming the width bounds it cannot derive. -/
macro "pbvClose" : tactic => `(tactic| ((veir_bv_normalize <;> pbv_decide 64 (blastWidth := 64))))

theorem widen_icmp_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_icmp (.type 1) .g_sext W) := by
  proveLegalValid with pbvClose

theorem custom_urem_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordBinary .g_remuw) := by
  proveLegalValid with pbvClose

theorem custom_ctlz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_clzw) := by
  proveLegalValid with pbvClose

theorem custom_cttz_valid : Puddle.CTree.Pattern.Valid (customLegalizeWordUnary .g_ctzw) := by
  proveLegalValid with pbvClose

/-- At the fixed width 64, beyond the blast width of `pbvClose`. -/
theorem custom_abs_valid : Puddle.CTree.Pattern.Valid customLegalizeAbs := by
  proveLegalValid with
    veir_bv_normalize
    pbv_decide 64

theorem widen_ctlz_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenCtlzSrc W) := by
  proveLegalValid with pbvClose

theorem widen_cttz_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenCttzSrc W) := by
  proveLegalValid with pbvClose

theorem widen_shl_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_shl (.type 1) .g_zext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

-- /-- Cannot prove the bound since values might be pointers which are unbounded -/
-- theorem widen_select_1_valid (W : Nat) (hW : W ≤ 64) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_select (.type 1) .g_zext W) := by
--   proveLegalValid with (veir_bv_normalize; pbv_decide 64)
--   all_goals sorry

/-! ## All widenings, up to 64 bits -/

theorem widen_add_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_add (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_sub_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_sub (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

/-- Predicate is abstracted -/
-- theorem widen_icmp_0_valid (W : Nat) (hW : W ≤ 64) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_icmp (.type 0) .g_anyext W) := by
--   proveLegalValid with pbvClose
--   all_goals sorry

theorem widen_select_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_select (.type 0) .g_anyext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_shl_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_shl (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_ashr_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ashr (.type 0) .g_sext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_lshr_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_lshr (.type 0) .g_zext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_ashr_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ashr (.type 1) .g_zext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_lshr_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_lshr (.type 1) .g_zext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_and_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_and (.type 0) .g_anyext W) := by
  proveLegalValid with pbvClose

theorem widen_or_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_or (.type 0) .g_anyext W clearDisjointProperties) := by
  proveLegalValid with pbvClose

theorem widen_xor_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_xor (.type 0) .g_anyext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

/-- At 8 bits: the multiplication times out at 16. -/
theorem widen_mul_0_valid (W : Nat) (hW : W ≤ 8) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_mul (.type 0) .g_anyext W clearNswNuwProperties) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 8)

-- Not pure `pbv_decide`: the UB checks of the division stay hypotheses, which `pbvClose` does
-- not use, so the case where only the target is UB needs them moved into the goal by hand.
-- theorem widen_sdiv_0_valid (W : Nat) (hW : W ≤ 8) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_sdiv (.type 0) .g_sext W) := by
--   proveLegalValid with
--     first
--       | (veir_bv_normalize; pbv_decide 8)
--       -- The target is UB but the source is not: move the two UB checks into the goal.
--       | (exfalso
--          rename_i hsrc htgt
--          revert hsrc htgt
--          veir_bv_normalize
--          -- `pbv_decide` abstracts the premises of a goal that concludes `False`.
--          try simp only [imp_false]
--          pbv_decide 8)

-- Not pure `pbv_decide`: the UB checks of the division stay hypotheses, which `pbvClose` does
-- not use, so the case where only the target is UB needs them moved into the goal by hand.
-- theorem widen_srem_0_valid (W : Nat) (hW : W ≤ 8) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_srem (.type 0) .g_sext W) := by
--   proveLegalValid with
--     first
--       | (veir_bv_normalize; pbv_decide 8)
--       -- The target is UB but the source is not: move the two UB checks into the goal.
--       | (exfalso
--          rename_i hsrc htgt
--          revert hsrc htgt
--          veir_bv_normalize
--          -- `pbv_decide` abstracts the premises of a goal that concludes `False`.
--          try simp only [imp_false]
--          pbv_decide 8)

-- Not pure `pbv_decide`: the UB checks of the division stay hypotheses, which `pbvClose` does
-- not use, so the case where only the target is UB needs them moved into the goal by hand.
-- theorem widen_udiv_0_valid (W : Nat) (hW : W ≤ 16) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_udiv (.type 0) .g_zext W) := by
--   proveLegalValid with
--     first
--       | (veir_bv_normalize; pbv_decide 16)
--       -- The target is UB but the source is not: move the two UB checks into the goal.
--       | (exfalso
--          rename_i hsrc htgt
--          revert hsrc htgt
--          veir_bv_normalize
--          -- `pbv_decide` abstracts the premises of a goal that concludes `False`.
--          try simp only [imp_false]
--          pbv_decide 16)

-- Not pure `pbv_decide`: the UB checks of the division stay hypotheses, which `pbvClose` does
-- not use, so the case where only the target is UB needs them moved into the goal by hand.
-- theorem widen_urem_0_valid (W : Nat) (hW : W ≤ 8) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_urem (.type 0) .g_zext W) := by
--   proveLegalValid with
--     first
--       | (veir_bv_normalize; pbv_decide 8)
--       -- The target is UB but the source is not: move the two UB checks into the goal.
--       | (exfalso
--          rename_i hsrc htgt
--          revert hsrc htgt
--          veir_bv_normalize
--          -- `pbv_decide` abstracts the premises of a goal that concludes `False`.
--          try simp only [imp_false]
--          pbv_decide 8)

-- False: the constant's attribute width is not tied to its result width (e.g. an `i1` attribute
-- on an `i7` result, value 2, widens to 0).
-- theorem widen_constant_0_valid (W : Nat) (hW : W ≤ 64) :
--     Puddle.CTree.Pattern.Valid (widenConstant W) := by
--   proveLegalValid with pbvClose
--   all_goals sorry

theorem widen_sext_inreg_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_sext_inreg (.type 0) .g_anyext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_ctlz_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ctlz (.type 0) .g_anyext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_cttz_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_cttz (.type 0) .g_anyext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_ctpop_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ctpop (.type 0) .g_anyext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_ctpop_1_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_ctpop (.type 1) .g_zext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

-- False below 16 bits, where `bswap` is the identity: the result reads back the extended high
-- bits (e.g. `i4` widened to 16 bits).
-- theorem widen_bswap_0_valid (W : Nat) (hW : W ≤ 64) :
--     Puddle.CTree.Pattern.Valid (widenReverse .g_bswap W) := by
--   proveLegalValid with pbvClose
--   all_goals sorry

theorem widen_bitreverse_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenReverse .g_bitreverse W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_smin_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_smin (.type 0) .g_sext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_smax_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_smax (.type 0) .g_sext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_umin_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_umin (.type 0) .g_sext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_umax_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_umax (.type 0) .g_sext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

theorem widen_abs_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_abs (.type 0) .g_sext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 64)

/-- At 16 bits: the funnel shift times out at 64. -/
theorem widen_fshl_1_valid (W : Nat) (hW : W ≤ 16) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_fshl (.type 1) .g_zext W) := by
  proveLegalValid with (veir_bv_normalize; pbv_decide 16)

/-- At 16 bits: the funnel shift times out at 64. -/
theorem widen_fshr_1_valid (W : Nat) (hW : W ≤ 16) :
    Puddle.CTree.Pattern.Valid (widenTypeGroup .g_fshr (.type 1) .g_zext W) := by
  proveLegalValid with (veir_bv_

theorem widen_uaddo_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_uaddo W) := by
  proveLegalValid with pbvClose

theorem widen_usubo_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_usubo W) := by
  proveLegalValid with pbvClose

theorem widen_saddo_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_saddo W) := by
  proveLegalValid with pbvClose

theorem widen_ssubo_0_valid (W : Nat) (hW : W ≤ 64) :
    Puddle.CTree.Pattern.Valid (widenScalarAddSubOverflow .g_ssubo W) := by
  proveLegalValid with pbvClose

-- Not a bit-vector goal: the loads read memory and choose the high bits of their results, so the
-- source's choice must be picked from the target's, in a `Sim` proof.
-- theorem widen_load_0_valid (W : Nat) (hW : W ≤ 64) :
--     Puddle.CTree.Pattern.Valid (widenTypeGroup .g_load (.type 0) .g_anyext W) := by
--   proveLegalValid with pbvClose
--   all_goals sorry

end Veir.Legalization.CTreeProofs.PBV
