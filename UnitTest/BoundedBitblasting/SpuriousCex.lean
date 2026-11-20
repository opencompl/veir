import Veir.Meta.Tactic.PBVDecide

/-!
# Checking counterexamples against the original goal

`bv_decide` counterexamples are decoded back to widths and values and checked
against the original, untranslated goal before they are reported as genuine.

## A spurious counterexample from the encoding of sums

The mask of a sum is linked to its parts by
`m_(u+v) = (1 <<< (cpop m_u + cpop m_v)) - 1` (`add_eq_shiftLeft_of_maskOfWidth`).
That lemma needs `u + v ≤ o`, but this bound is a `Nat` fact and is cleared
before `bv_decide` runs. When `cpop m_u + cpop m_v ≥ o` the shift saturates, so
`m_(u+v)` becomes all ones, which decodes to the width `o` rather than to `u + v`.

Below, the blast width is `o = 4`. The model `u = v = 4` satisfies every mask
constraint (`m_(u+v) = 0xf ≤ m_4 = 0xf`), even though `u + v ≤ 4` rules it out
over `Nat`. Nothing is abstracted, so only the check against the original goal
reveals that the counterexample is spurious.
-/

-- The statement is true: `u + v ≤ 4` and `u = 4` force `v = 0`, and `BitVec 0`
-- has a single element.
theorem spurious_true (u v : Nat) (h : u + v ≤ 4) (hu : u = 4) (y z : BitVec v) :
    y = z := by
  obtain rfl : v = 0 := by omega
  exact Subsingleton.elim y z

-- The values of `y` and `z` depend on the SAT model, so only the widths are matched.
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The assignment does not falsify the original goal: it violates the hypothesis h : 4 + 4 ≤ 4.
Consider the following assignment:
  u = 4  	(m_u = 0xf#4)
  u + v = 4  	(m_u_add_v = 0xf#4)
  v = 4  	(m_v = 0xf#4)
-/
#guard_msgs(error, substring := true) in
example (u v : Nat) (h : u + v ≤ 4) (hu : u = 4) (y z : BitVec v) :
    y = z := by
  pbv_decide 2

/-! ## Confirmed counterexamples -/

-- A false statement: the counterexample falsifies the original goal.
-- The values depend on the SAT model, so only the check is matched.
/--
The assignment satisfies the hypotheses and falsifies the original goal.
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) : x + y = x := by
  pbv_decide 4

-- `1#(w + 0)` is abstracted as an opaque variable, but the decoded assignment
-- still falsifies the original goal, so the counterexample is genuine.
/--
The assignment satisfies the hypotheses and falsifies the original goal.
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) (hw1 : 0 < w) :
    x + (1 : BitVec (w + 0)) = x := by
  pbv_decide 4
