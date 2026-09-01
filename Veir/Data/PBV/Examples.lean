module

meta import Std.Tactic.BVDecide.Reflect

import Std.Tactic.BVDecide
import Veir.Data.PBV.Elim
import Veir.Data.PBV.Push

/-! # Manual traces of the bounded parametric bitvector pipeline.

Each example works through the steps documented in `Veir.Data.PBV` by hand.
-/

namespace Veir.Data.PBV

/-- Manual trace of the future tactic, transforming an unbounded parametric width
    statement into a bounded one and solving it up to the bound (4 in this case) -/
theorem trace_add_comm_manual (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
-- Step 1: Bound widths to the provided blast width (redundant in this case)
  have w_le_bw : w ≤ 4 := by grind
-- Step 2-3: Introduce mask to replace `w` Nat var
  apply width_elim 4 w
  intro mw h_mw
-- Step 4: Eliminate the parametric bv var of width `w`
--         enforcing width constraint with mask
  revert x
  apply var_elim 4 w w_le_bw
  intro x h_xmw
  revert y
  apply var_elim 4 w w_le_bw
  intro y h_ymw
-- Step 5: Convert width hypothesis to mask hypothesis
  have mw_mask := isMask_of_eq_maskOfWidth h_mw
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
      eq_iff w_le_bw,             -- Introduce `setWidth` to goal
      setWidth_add w_le_bw,       -- Push `setWidth` down add
      setWidth_setWidth w_le_bw,  -- Push `setWidth` down setWidth
      BitVec.setWidth_eq,         -- Remove redundant setWidths
      ← h_mw]                     -- Replace mask with nat with bv constraint
      at h_xmw h_ymw ⊢
-- Step 7: Drop the Nat `w`
  clear hw
  clear w_le_bw h_mw
  clear w
-- Step 8: Bitblast!
  bv_decide

/-- Manual trace of a zero extension to `q` followed by a zero extension to `r`,
    which is a single zero extension to `r`, for all widths `p < q < r ≤ 8` -/
theorem trace_double_zero_extend (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
-- Step 1: Bound widths to the provided blast width
  have r_le_bw : r ≤ 8 := by grind
  have q_le_bw : q ≤ 8 := by grind
  have p_le_bw : p ≤ 8 := by grind
-- Step 2-3: Introduce mask to replace `w` Nat var
  apply width_elim 8 r
  intro mr h_mr
  apply width_elim 8 q
  intro mq h_mq
  apply width_elim 8 p
  intro mp h_mp
-- Step 4: Eliminate the parametric bv var of width `w`
--         enforcing width constraint with mask
  revert x
  apply var_elim 8 p p_le_bw
  intro x h_xmp
-- Step 5: Convert width hypothesis to mask hypothesis
  have mr_mask := isMask_of_eq_maskOfWidth h_mr
  have mq_mask := isMask_of_eq_maskOfWidth h_mq
  have mp_mask := isMask_of_eq_maskOfWidth h_mp
-- Step 5B: Translate the condition on the natural number width
--   into a fact about the bitvector masks
  have lt_pq := mask_lt_mask p_le_bw q_le_bw h_mp h_mq hpq
  simp only [isMask_eq] at mr_mask mq_mask mp_mask
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
    eq_iff r_le_bw,
    setWidth_setWidth r_le_bw,
    setWidth_setWidth p_le_bw,
    setWidth_setWidth q_le_bw,
    BitVec.zeroExtend_eq_setWidth,
    BitVec.setWidth_eq,
    ← h_mr,
    ← h_mq,
    ← h_mp,
  ] at h_xmp ⊢
-- Step 7: Drop the Nat 'p', 'q', 'r'
  clear h_mp h_mq h_mr
  clear hr hqr hpq r_le_bw q_le_bw p_le_bw
  clear p q r
-- Step 8: Bitblast!
  bv_decide

/-- Manual trace of a zero extension to `q` followed by a sign extension to `r`,
    which is a single zero extension to `r`, since `p < q` leaves the sign bit
    of the intermediate value clear -/
theorem trace_zero_sign_extend (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).signExtend r = x.zeroExtend r
  := by
-- Step 1: Bound widths to the provided blast width
  have r_le_bw : r ≤ 8 := by grind
  have q_le_bw : q ≤ 8 := by grind
  have p_le_bw : p ≤ 8 := by grind
-- Step 2-3: Introduce mask to replace `w` Nat var
  apply width_elim 8 r
  intro mr h_mr
  apply width_elim 8 q
  intro mq h_mq
  apply width_elim 8 p
  intro mp h_mp
-- Step 4: Eliminate the parametric bv var of width `w`
--         enforcing width constraint with mask
  revert x
  apply var_elim 8 p p_le_bw
  intro x h_xmp
-- Step 5: Convert width hypothesis to mask hypothesis
  have mr_mask := isMask_of_eq_maskOfWidth h_mr
  have mq_mask := isMask_of_eq_maskOfWidth h_mq
  have mp_mask := isMask_of_eq_maskOfWidth h_mp
-- Step 5B: Translate the condition on the natural number width
--   into a fact about the bitvector masks
  have lt_pq := mask_lt_mask p_le_bw q_le_bw h_mp h_mq hpq
  simp only [isMask_eq] at mr_mask mq_mask mp_mask
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
    eq_iff r_le_bw,
    setWidth_signExtend_eq_and_maskOfWidth,                -- Push `setWidth` down signExtend
    msb_eq_and_signBitOfMask_maskOfWidth_ne_zero q_le_bw,  -- Sign bit test becomes a mask test
    setWidth_setWidth r_le_bw,
    setWidth_setWidth q_le_bw,
    setWidth_setWidth p_le_bw,
    BitVec.zeroExtend_eq_setWidth,
    signBitOfMask,                 -- Unfold, else `bv_decide` abstracts it away
    BitVec.setWidth_eq,
    q_le_bw,                       -- Lets simp discharge the `v ≤ o` side condition of
                                   -- `setWidth_signExtend_eq_and_maskOfWidth`
    ← h_mr,
    ← h_mq,
    ← h_mp,
  ] at h_xmp ⊢
-- Step 7: Drop the Nat 'p', 'q', 'r'
  clear h_mp h_mq h_mr
  clear hr hqr hpq r_le_bw q_le_bw p_le_bw
  clear p q r
-- Step 8: Bitblast!
  bv_decide
