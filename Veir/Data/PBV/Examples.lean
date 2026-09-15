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
  apply var_elim w_le_bw h_mw
  intro x x_xmw
  revert y
  apply var_elim w_le_bw h_mw
  intro y h_ymw
-- Step 5: Convert width hypothesis to mask hypothesis
  have mw_mask := and_add_one_eq_zero_of_maskOfWidth h_mw
-- Step 5B: Translate the width precondition `w ≤ 4` into `mw ≤ BitVec.ofNat 4 (2 ^ 4 - 1)`
  let lit4 : BitVec 4 := 15#4
  have h_lit4_mask : lit4 = maskOfWidth 4 4 := by rfl
  have bv_hw := le_of_le_of_eq_maskOfWidth w_le_bw (by decide) h_mw h_lit4_mask hw
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [eq_iff (o := 4) w_le_bw, setWidth_add w_le_bw, setWidth_setWidth w_le_bw, BitVec.setWidth_eq, BitVec.setWidth_eq, ← h_mw]
-- Step 7: Clear the widths
  clear h_mw w_le_bw hw w
-- Step 8: Bitblast!
  bv_decide


/-- Manual trace of a zero extension to `q` followed by a zero extension to `r`,
    which is a single zero extension to `r`, since `p < q`.
-/
theorem trace_zero_zero_extend (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (h_qr : q < r)
  (h_pq : p < q) :
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
  apply var_elim p_le_bw h_mp
  intro x h_xmp
-- Step 5: Convert width hypothesis to mask hypothesis
  have mr_mask := and_add_one_eq_zero_of_maskOfWidth h_mr
  have mq_mask := and_add_one_eq_zero_of_maskOfWidth h_mq
  have mp_mask := and_add_one_eq_zero_of_maskOfWidth h_mp
-- Step 5B: Translate the condition on the natural number width
--          into a fact about the bitvector masks
  let lit8 : BitVec 8 := 255#8
  have h_lit8_mask : lit8 = maskOfWidth 8 8 := by rfl
  have bv_hr := le_of_le_of_eq_maskOfWidth r_le_bw (by decide) h_mr h_lit8_mask hr
  have bv_p_lt_q := lt_of_lt_of_eq_maskOfWidth p_le_bw q_le_bw h_mp h_mq h_pq
  have bv_q_lt_r := lt_of_lt_of_eq_maskOfWidth q_le_bw r_le_bw h_mq h_mr h_qr
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
    eq_iff (o := 8) r_le_bw,
    setWidth_setWidth,
    BitVec.zeroExtend_eq_setWidth,
    BitVec.setWidth_eq,
    p_le_bw,
    q_le_bw,
    r_le_bw,
    ← h_mp,
    ← h_mq,
    ← h_mr,
  ]
  clear h_mp h_mq h_mr r_le_bw q_le_bw p_le_bw h_qr h_pq hr p q r
-- Step 8: BitBlast!
  bv_decide

/-- Manual trace of a double zero extension where the width condition is encoded
    as a conjunction of two inequalities. Only step 5B differs from the above. -/
theorem trace_zero_zero_extend_conj (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (h : q < r ∧ p < q) :
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
  apply var_elim p_le_bw h_mp
  intro x h_xmp
-- Step 5: Convert width hypothesis to mask hypothesis
  have mr_mask := and_add_one_eq_zero_of_maskOfWidth h_mr
  have mq_mask := and_add_one_eq_zero_of_maskOfWidth h_mq
  have mp_mask := and_add_one_eq_zero_of_maskOfWidth h_mp
-- Step 5B: Translate the condition on the natural number width
--          into a fact about the bitvector masks
  let lit8 : BitVec 8 := 255#8
  have h_lit8_mask : lit8 = maskOfWidth 8 8 := by rfl
  have bv_hr := le_of_le_of_eq_maskOfWidth r_le_bw (by decide) h_mr h_lit8_mask hr
  have bv_h : mq < mr ∧ mp < mq := by
    apply And.intro
    · apply lt_of_lt_of_eq_maskOfWidth q_le_bw r_le_bw h_mq h_mr (And.left h)
    · apply lt_of_lt_of_eq_maskOfWidth p_le_bw q_le_bw h_mp h_mq (And.right h)
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
    eq_iff (o := 8),
    setWidth_setWidth,
    BitVec.zeroExtend_eq_setWidth,
    BitVec.setWidth_eq,
    p_le_bw,
    r_le_bw,
    q_le_bw,                       -- Lets simp discharge the `w ≤ o` side condition of
                                   -- `setWidth_setWidth`
    ← h_mp,
    ← h_mr,
    ← h_mq,
  ]
  clear h_mp h_mr h_mq
  clear h r_le_bw p_le_bw q_le_bw hr p q r
-- Step 8: BitBlast!
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
  apply var_elim p_le_bw h_mp
  intro x h_xmp
-- Step 5: Convert width hypothesis to mask hypothesis
  have mr_mask := and_add_one_eq_zero_of_maskOfWidth h_mr
  have mq_mask := and_add_one_eq_zero_of_maskOfWidth h_mq
  have mp_mask := and_add_one_eq_zero_of_maskOfWidth h_mp
-- Step 5B: Translate the condition on the natural number width
--          into a fact about the bitvector masks
  let lit8 : BitVec 8 := 255#8
  have h_lit8_mask : lit8 = maskOfWidth 8 8 := by rfl
  have bv_hr := le_of_le_of_eq_maskOfWidth r_le_bw (by decide) h_mr h_lit8_mask hr
  have bv_p_lt_q := lt_of_lt_of_eq_maskOfWidth p_le_bw q_le_bw h_mp h_mq hpq
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
    eq_iff (o := 8),
    msb_eq_and_signBitOfMask_maskOfWidth_ne_zero (o := 8),          -- Replace the sign bit test with a mask test
    setWidth_signExtend_eq_and_maskOfWidth,          -- Push `setWidth` down signExtend
    BitVec.zeroExtend_eq_setWidth,
    setWidth_setWidth,
    signBitOfMask_eq,                 -- Unfold, else `bv_decide` abstracts it away
    BitVec.setWidth_eq,
    p_le_bw,
    r_le_bw,
    q_le_bw,                       -- Lets simp discharge the `v ≤ o` side condition of
                                   -- `setWidth_signExtend_eq_and_maskOfWidth`
    ← h_mr,
    ← h_mq,
    ← h_mp,
  ]
  clear h_mp h_mr h_mq
  clear hr hqr hpq
  clear r_le_bw p_le_bw q_le_bw p q r
-- Step 8: BitBlast!
  bv_decide

/-- Manual trace of an append, whose result is twice as wide as its operands,
    so the blast width has to cover `w + w` rather than just `w`. -/
theorem trace_append (w : Nat) (a b : BitVec w) (hw : w ≤ 8) :
  (a ++ b) + (b ++ a) = (a ++ a) + (b ++ b)
  := by
-- Step 1: Bound widths to the provided blast width. The blast width is 16, not
--         8, because every append here has width `w + w`.
  have w_le_bw : w ≤ 16 := by grind
  have w_add_w_le_bw : w + w ≤ 16 := by grind
-- Step 2-3: Introduce masks to replace the `w` and `w + w` Nat widths.
  apply width_elim 16 w
  intro mw h_mw
  apply width_elim 16 (w + w)
  intro mw_add_w h_mw_add_w
-- Step 4: Eliminate the parametric bv vars of width `w`
--         enforcing width constraint with mask.
  revert a
  apply var_elim w_le_bw h_mw
  intro a h_amw
  revert b
  apply var_elim w_le_bw h_mw
  intro b h_bmw
-- Step 5: Convert width hypothesis to mask hypothesis.
  have mw_mask := and_add_one_eq_zero_of_maskOfWidth h_mw
  have w_add_w_mask := add_eq_mul_of_maskOfWidth w_le_bw w_le_bw w_add_w_le_bw h_mw h_mw h_mw_add_w
-- Step 5B: Translate the width precondition `w ≤ 8` into `mw ≤ BitVec.ofNat 16 (2 ^ 8 - 1)`
  let lit8 : BitVec 16 := 255#16
  have h_lit8_mask : lit8 = maskOfWidth 16 8 := by rfl
  have bv_hw := le_of_le_of_eq_maskOfWidth w_le_bw (by decide) h_mw h_lit8_mask hw
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down.
  simp only [
    eq_iff (o := 16),
    setWidth_add,
    setWidth_append_eq_or_mul_maskOfWidth_add_one (o := 16),
    setWidth_setWidth,
    w_add_w_le_bw,                 -- Lets simp discharge the `v + w ≤ o` side condition of
                                   -- `setWidth_append_eq_or_mul_maskOfWidth_add_one`.
    w_le_bw,
    ← h_mw,
    ← h_mw_add_w,
    BitVec.setWidth_eq
  ]
-- Step 7: Rewrite the mask into the hypotheses too.
  clear h_mw h_amw h_bmw h_mw_add_w
  clear w_le_bw w_add_w_le_bw
  clear hw w
-- Step 8: BitBlast!
  bv_decide
