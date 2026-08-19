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
