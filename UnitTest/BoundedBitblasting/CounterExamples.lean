import Veir.Meta.Tactic.PBVDecide

/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  p = 7  	(m_w0 = 0x7f#8)
  r = 8  	(m_w1 = 0xff#8)
  q = 0  	(m_w2 = 0x00#8)
  x = 0x7f#7
-/
#guard_msgs in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : q < p) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8

/--
error: The prover found a counterexample, consider the following assignment:
m_w1 = 255#8
m_w2 = 0#8
m_w0 = 127#8
x = 127#8
-/
#guard_msgs in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : q < p) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8 -bv_decide
  bv_decide

/--
warning: `grind` could not prove the following : q ≤ 8
---
error: unsolved goals
p q r : Nat
x : BitVec p
hr : r ≤ 8
h_qp : p < q
h_pr : p < r
m_w1 : BitVec 8
h_m_w1 : m_w1 = Veir.Data.PBV.maskOfWidth 8 r
h_m_w1_le_blast : r ≤ 8
h_m_w1_bv_mask : m_w1 &&& m_w1 + 1#8 = 0#8
m_w2 : BitVec 8
h_m_w2 : m_w2 = Veir.Data.PBV.maskOfWidth 8 q
⊢ q ≤ 8
-/
#guard_msgs in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : p < q) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8

/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  w = 4  	(m_w0 = 0xf#4)
  x = 0xf#4
  y = 0xf#4
-/
#guard_msgs in
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
    x + y = x := by
  pbv_decide 4

-- Every composite width gets its own mask, reported next to the `Nat` value it encodes
/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  w = 4  	(m_w0 = 0x0f#8)
  w + v = 8  	(m_w0_add_w1 = 0xff#8)
  v = 4  	(m_w1 = 0x0f#8)
  v + w = 8  	(m_w1_add_w0 = 0xff#8)
  x = 0xe#4
  y = 0xf#4
-/
#guard_msgs in
example (v w : Nat) (x : BitVec v) (y : BitVec w) (hv : v ≤ 4) (hw : w ≤ 4) (h : v = w) :
    x ++ y = (y ++ x).setWidth (v + w) := by
  pbv_decide 4

/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  4 + w = 8  	(m_lit4_add_w0 = 0x0ff#12)
  w = 4  	(m_w0 = 0x00f#12)
  x = 0xf#4
-/
#guard_msgs in
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
    (0#4 ++ x).setWidth 4 = 0#4 := by
  pbv_decide 8

-- A width only mentioned in a hypothesis is reported alongside the sum it is equal to
/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  w = 4  	(m_w0 = 0x0f#5)
  w + 1 = 5  	(m_w0_add_lit1 = 0x1f#5)
  v = 5  	(m_w2 = 0x1f#5)
  x = 0xf#4
-/
#guard_msgs in
example (v w : Nat) (x : BitVec w) (hw : w ≤ 4) (hv : v = w + 1) :
    (x.zeroExtend v).msb = x.msb := by
  pbv_decide 4

/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  p = 7  	(m_w0 = 0x7f#8)
  r = 8  	(m_w1 = 0xff#8)
  x = 0x7f#7
-/
#guard_msgs in
example (p r : Nat) (x : BitVec p) (hr : r ≤ 8) (h : p < r) :
    x.signExtend r = x.zeroExtend r := by
  pbv_decide 8

-- The counterexample can pick a width of zero
/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  p = 8  	(m_w0 = 0xff#8)
  w = 0  	(m_w1 = 0x00#8)
  x = 0xff#8
-/
#guard_msgs in
example (p w : Nat) (x : BitVec p) (hp : p ≤ 8) (hwp : w < p) :
    (x.setWidth w).msb = x.msb := by
  pbv_decide 8

-- A "potentially spurious" counterexample can still be genuine: at `w = 0`, `1#0 = 0#0`
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.ofBool (BitVec.setWidth w x + 1#w == BitVec.setWidth w x) = 0x1#1
Consider the following assignment:
  w = 0  	(m_w0 = 0x0#4)
  x = 0x0#0
-/
#guard_msgs in
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
    x + 1#w ≠ x := by
  pbv_decide 4

-- Expected failure: `setWidth` is not pushed through `*`, so the products are abstracted
-- and a true statement gets a spurious counterexample
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.setWidth 4 (BitVec.setWidth w x * BitVec.setWidth w y) = 0xf#4
    - BitVec.setWidth 4 (BitVec.setWidth w y * BitVec.setWidth w x) = 0x7#4
Consider the following assignment:
  w = 4  	(m_w0 = 0xf#4)
  x = 0xf#4
  y = 0xf#4
-/
#guard_msgs in
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
    x * y = y * x := by
  pbv_decide 4

/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.setWidth 4 (BitVec.setWidth w x * BitVec.setWidth w y) = 0x7#4
Consider the following assignment:
  w = 4  	(m_w0 = 0xf#4)
  x = 0xf#4
  y = 0xf#4
-/
#guard_msgs in
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
    x * y = x := by
  pbv_decide 4

-- Without a bound on `w` the side goal is left to the user, but the counterexample is still reported
/--
warning: `grind` could not prove the following : w ≤ 4
---
error: `pbv_decide` found a counterexample, consider the following assignment:
  w = 4  	(m_w0 = 0xf#4)
  x = 0xf#4
  y = 0xf#4
-/
#guard_msgs in
example (w : Nat) (x y : BitVec w) :
    x + y = x := by
  pbv_decide 4

-- The bound must also cover widths built from literals: `w + 2` can exceed 4
/--
warning: `grind` could not prove the following : w + 2 ≤ 4
---
error: unsolved goals
w : Nat
x y : BitVec (w + 2)
hw : w ≤ 4
m_w0 : BitVec 4
h_m_w0 : m_w0 = Veir.Data.PBV.maskOfWidth 4 (w + 2)
⊢ w + 2 ≤ 4
-/
#guard_msgs in
example (w : Nat) (x y : BitVec (w + 2)) (hw : w ≤ 4) :
    x + y = y + x := by
  pbv_decide 4
