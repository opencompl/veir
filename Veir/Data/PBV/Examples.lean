module

meta import Std.Tactic.BVDecide.Reflect

import Std.Tactic.BVDecide
import Veir.Data.PBV.Elim
import Veir.Data.PBV.Push

/-! # Manual traces of the bounded parametric bitvector pipeline.

Each example works through the steps documented in `Veir.Data.PBV` by hand, in the order the
tactic will eventually perform them; the comments refer to that numbering.
-/

namespace Veir.Data.PBV

/-- Manual trace of the pbvn_to_1 tactic, transforming an unbounded parametric width
    statement into a bounded one and solving it up the bound (4 in this case) -/
theorem trace_add_comm_manual (w : Nat) (x y : BitVec w)
  (hw : w ≤ 4)
  : x + y = y + x := by
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
  have mw_mask := mask_isMask w_le_bw h_mw
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

/-- Manual trace of the pbvn_to_1 tactic, transforming an unbounded parametric width
    statement into a bounded one and solving it up the bound (4 in this case) -/
theorem trace_add_comm_manual_calc (w : Nat) (x y : BitVec w)
  (hw : w ≤ 4)
  : x + y = y + x := by
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
  have mw_mask := mask_isMask w_le_bw h_mw
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  generalize h_xw : BitVec.setWidth w x = xw
  generalize h_yw : BitVec.setWidth w y = yw
  have push :=
    calc (xw + yw = yw + xw)
      -- Introduce `setWidth` to goal
      _ = (BitVec.setWidth 4 (xw + yw) = BitVec.setWidth 4 (yw + xw)) :=
        eq_iff w_le_bw _ _
      -- Push `setWidth` down add, masking the result
      _ = ((BitVec.setWidth 4 xw + BitVec.setWidth 4 yw) &&& mw
         = (BitVec.setWidth 4 yw + BitVec.setWidth 4 xw) &&& mw) := by
        rw [setWidth_add w_le_bw, setWidth_add w_le_bw, ← h_mw]
      -- Push `setWidth` down setWidth, unfolding `xw`, `yw` to reach the leaves `x`, `y`
      _ = (((BitVec.setWidth 4 x &&& mw) + (BitVec.setWidth 4 y &&& mw)) &&& mw
         = ((BitVec.setWidth 4 y &&& mw) + (BitVec.setWidth 4 x &&& mw)) &&& mw) := by
        rw [← h_xw, ← h_yw, setWidth_setWidth w_le_bw, setWidth_setWidth w_le_bw, ← h_mw]
      -- Remove redundant setWidths
      _ = (((x &&& mw) + (y &&& mw)) &&& mw = ((y &&& mw) + (x &&& mw)) &&& mw) := by
        rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
  rw [push]
  rw [← h_mw] at h_xmw h_ymw
  clear push h_xw h_yw xw yw
-- Step 7: Drop the Nat `w`
  clear hw
  clear w_le_bw h_mw
  clear w
-- Step 8: Bitblast!
  bv_decide
