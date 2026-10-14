import Veir.Meta.Tactic.PBVDecide

-- Truncating to a width below the source loses bits that widening cannot recover
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : q < p) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8

-- With `-bv_decide` the goal is handed back, and `bv_decide` finds the counterexample instead
/--
error: The prover found a counterexample
-/
#guard_msgs(error, substring := true) in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : q < p) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8 -bv_decide
  bv_decide

-- Every width must be bounded, even when the statement holds: `q` can exceed 8
/--
warning: `grind` could not prove the following : q ≤ 8
---
error: unsolved goals
-/
#guard_msgs(error, warning, substring := true) in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : p < q) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8

-- A false equation over a single bounded width
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
    x + y = x := by
  pbv_decide 4

-- Masks are named after the width variables they encode
/--
(m_v_add_w =
-/
#guard_msgs(error, substring := true) in
example (v w : Nat) (x : BitVec v) (y : BitVec w) (hv : v ≤ 4) (hw : w ≤ 4) (h : v = w) :
    x ++ y = (y ++ x).setWidth (v + w) := by
  pbv_decide 4

-- Widths mixing literals and variables
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
    (0#4 ++ x).setWidth 4 = 0#4 := by
  pbv_decide 8

-- A width only mentioned in a hypothesis is reported alongside the sum it is equal to
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (v w : Nat) (x : BitVec w) (hw : w ≤ 4) (hv : v = w + 1) :
    (x.zeroExtend v).msb = x.msb := by
  pbv_decide 4

-- `signExtend` and `zeroExtend` differ whenever the msb is set
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (p r : Nat) (x : BitVec p) (hr : r ≤ 8) (h : p < r) :
    x.signExtend r = x.zeroExtend r := by
  pbv_decide 8

-- The counterexample can pick a width of zero
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (p w : Nat) (x : BitVec p) (hp : p ≤ 8) (hwp : w < p) :
    (x.setWidth w).msb = x.msb := by
  pbv_decide 8

-- A statement that is false at width `w = 0`
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
    x + 1#w ≠ x := by
  pbv_decide 4

-- Without a bound on `w` the side goal is left to the user, but the counterexample is still reported
/--
warning: `grind` could not prove the following : w ≤ 4
---
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, warning, substring := true) in
example (w : Nat) (x y : BitVec w) :
    x + y = x := by
  pbv_decide 4

-- The counterexample can pick a width of zero
/--
error: `pbv_decide` found a counterexample
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (y : BitVec 4) (hw : w ≤ 4) :
    (y.setWidth w).zeroExtend 4 = y := by
  pbv_decide 4

-- Expected failure: a constant at width `w + 0` is not pushed, as `w + 0` is not syntactically `w`
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.setWidth 4 1#(w + 0)
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
    x + (1 : BitVec (w + 0)) = 1 + x := by
  pbv_decide 4

-- Expected failure: width expressions using `Nat` subtraction are not translated faithfully
-- Expected failure: the widths `v - 1 - 0 + 1` are translated, but `extractLsb'` is not pushed
/--
`pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
-/
#guard_msgs(error, substring := true) in
example {v : Nat} (x : BitVec w) (hw : w ≤ 8) (hv : v ≤ w) (hv1 : v > 0):
    (x.extractLsb (v-1) 0).cast (by lia) = (x &&& ((1#w <<< BitVec.ofNat w v) - 1)).setWidth v := by
  pbv_decide 8

-- A width built by subtraction is translated faithfully, so the counterexample is genuine
/--
error: `pbv_decide` found a counterexample, consider the following assignment:
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x : BitVec (w - 1)) (hw : w ≤ 4) :
    x.zeroExtend w = x.signExtend w := by
  pbv_decide 4

-- Expected failure: `w / 2` is a width independent of `w`, so a true statement fails spuriously
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following widths were abstracted as independent variables:
    - w / 2
-/
#guard_msgs(error, substring := true) in
example (w : Nat) (x : BitVec (w / 2)) (hw : w ≤ 4) :
    (x.setWidth w).setWidth (w / 2) = x := by
  pbv_decide 4

-- Expected failure, width in `extractLsb'` is not converted to mask
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.ofNatClamp 4 (w - 1)
-/
#guard_msgs(error, substring := true) in
example (a : BitVec w) (h : w ≤ 4) :
    (a.extractLsb' (w - 1) 1 == 1) = a.msb := by
  pbv_decide 4

-- `w + w` correctly interpreted as a sum of widths
/--
`pbv_decide` found a counterexample, consider the following assignment:
-/
#guard_msgs(error, substring := true) in
example (a : BitVec (w + w)) (b : BitVec w) (hw4 : w + w ≤ 4):
  a ++ b = (b ++ a).cast (by grind)
  := by
  pbv_decide 4
