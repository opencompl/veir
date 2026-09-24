import Veir.Meta.Tactic.PBVDecide

/--
error: `pbv_decide` found a counterexample, consider the following assignment:
  r = 8  	(m_w1 = 0xff#8)
  q = 0  	(m_w2 = 0x00#8)
  p = 7  	(m_w0 = 0x7f#8)
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
  pbv_decide? 8
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

-- Expected failure: at the blast width, the `setWidth` around `signExtend` is simplified away before `signExtend` is pushed
/--
error: `pbv_decide` found a potentially spurious counterexample.
  The following expressions were abstracted as opaque variables:
    - BitVec.signExtend 4 (BitVec.setWidth w x) = 0xd#4
Consider the following assignment:
  w = 2  	(m_w0 = 0x3#4)
  x = 0x3#2
-/
#guard_msgs in
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
    (x.signExtend 4).setWidth w = x := by
  pbv_decide 4
