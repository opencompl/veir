import Veir.Meta.Tactic.PBVDecide

/-- Commutativity of addition -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4

/-- Commutativity of addition with definitionally-not-syntactically equal widths -/
example (w : Nat) (x : BitVec (w + 0)) (y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4

/-- Commutativity of addition for three variables -/
example (w : Nat) (x y z : BitVec w) (hw : w ≤ 4) :
  x + y + z = y + x + z := by
  pbv_decide 4

/-- Appending and adding -/
example (w : Nat) (a b : BitVec w) (hw : w ≤ 8) :
  (a ++ b) + (b ++ a) = (a ++ a) + (b ++ b) := by
  pbv_decide 8

/-- Extending, adding and truncating is the same as adding -/
example {w t v: Nat} (a b : BitVec w)
  (exta extb : BitVec v)
  (hqw : w ≤ t)
  (hv : t = v + w)
  (bound : t ≤ 32):
  a + b = ((exta ++ a) + (extb ++ b)).setWidth w
  := by
  pbv_decide 16

/-- Zero extending a zero extension (≤, <) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p ≤ q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8

/-- Zero extending a zero extension (≥, >) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : r > q)
  (hpq : q ≥ p) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8

/-- Double zero extending with conjunction condition -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (h : q < r ∧ p < q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8

/-- Double zero extending with composite width -/
example (p q : Nat) (x : BitVec p)
  (hq : q ≤ 8)
  (hqp : q > p) :
  (x.zeroExtend q).zeroExtend (q + q) = x.zeroExtend (q + q)
  := by
  pbv_decide 8

/-- Sign extending a sign extension -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q ≤ r)
  (hpq : p ≤ q) :
  (x.signExtend q).signExtend r = x.signExtend r
  := by
  pbv_decide 8

/-- Sign extending a zero extension -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).signExtend r = x.zeroExtend r
  := by
  pbv_decide 8

/-- Resizing preserves the msb iff the width is unchanged -/
example (p w : Nat) (x : BitVec p)
  (hp : p ≤ 8)
  (hwp : w = p) :
  (x.setWidth w).msb = x.msb
  := by
  pbv_decide 8

/-- A goal width defined by a sum only mentioned in a hypothesis (`=`). -/
example (w v t : Nat) (x : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (ht : t = w + v) :
  (x.zeroExtend t).setWidth w = x := by
  pbv_decide 4

/-- Nested sum in a hypothesis requires a blast width of three times the bound. -/
example (u v w t : Nat) (x : BitVec w) (hu : u ≤ 4) (hv : v ≤ 4) (hw : w ≤ 4)
  (ht : t = u + v + w) :
  (x.zeroExtend t).setWidth w = x := by
  pbv_decide 4

/-- Sum in a hypothesis larger than any sum in the goal. -/
example (w v : Nat) (a b : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w + w ≤ w + w + v) :
  (a ++ b) + (b ++ a) = (a ++ a) + (b ++ b) := by
  pbv_decide 4

/-- Sums in a hypothesis under a conjunction contribute to the blast width. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w ≤ w + v ∧ v ≤ w + v) :
  x + y = y + x := by
  pbv_decide 4

/-- Sums in a hypothesis using `≥` contribute to the blast width. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w + v ≥ v) :
  x + y = y + x := by
  pbv_decide 4

/-- Sums on both sides of a `<` hypothesis contribute to the blast width. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w + w < w + v) :
  x + y = y + x := by
  pbv_decide 4

/-- Appending to a bitvector of literal width -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 10) :
  0#4 ++ x = x.zeroExtend (4 + w) := by
  pbv_decide 10

/-- Zero-extending by a literal amount preserves the value -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 8) :
  (x.zeroExtend (w + 2)).setWidth w = x := by
  pbv_decide 8

/-- A hypothesis containing a literal above the blast width -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) (h : w < 9) :
  x + y = y + x := by
  pbv_decide 4

/-- Appending a literal-width bitvector as the low part -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
  x ++ 0#2 = (x ++ 0#1) ++ 0#1 := by
  pbv_decide 4

/-- Equality at a literal width -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
  (x ++ 0#2).setWidth 2 = 0#2 := by
  pbv_decide 4

/-- A variable of literal width above the bound -/
example (w : Nat) (x y : BitVec w) (a b : BitVec 4) (hw : w ≤ 2) :
  x + y = y + x ∧ a + b = b + a := by
  pbv_decide 2

/-- A conjunction with a literal above the blast width -/
example (w : Nat) (x y : BitVec w) (h : w ≤ 4 ∧ w < 9) :
  x + y = y + x := by
  pbv_decide 4

/-- A variable whose width is a raw `nat_lit` -/
example (w : Nat) (x y : BitVec w) (a b : BitVec (nat_lit 4)) (hw : w ≤ 4) :
  x + y = y + x ∧ a + b = b + a := by
  pbv_decide 4

/-- A variable of width zero -/
example (w : Nat) (x : BitVec w) (z : BitVec 0) (hw : w ≤ 4) :
  x ++ z = x ++ 0#0 := by
  pbv_decide 4

/-- The same literal as a variable width and in a hypothesis -/
example (w : Nat) (x : BitVec w) (a : BitVec 4) (hw : w ≤ 4) :
  (a ++ x).setWidth w = x := by
  pbv_decide 4

/-- Sign extension to a literal width below the blast width -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
  (x.signExtend 3).setWidth w = x := by
  pbv_decide 4

/-- A sum with a literal on the larger side of a hypothesis -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) (h : 1 ≤ w + 2) :
  x + y = y + x := by
  pbv_decide 4

/-- A variable whose width is a sum with a literal -/
example (w : Nat) (x y : BitVec (w + 2)) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 6 -- Need to extend the bound to account for the w + 2

example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
    (x.signExtend 4).setWidth w = x := by
  pbv_decide 4

-- # Expected Failures

-- Expected failure: at the blast width, the `setWidth` around `signExtend` is simplified away before `signExtend` is pushed
/--
error: The prover found a potentially spurious counterexample:
- It abstracted the following unsupported expressions as opaque variables:
  - BitVec.signExtend 4 (BitVec.setWidth w x)
Consider the following assignment:
m_w0 = 3#4
x = 3#4
BitVec.signExtend 4 (BitVec.setWidth w x) = 13#4
-/
#guard_msgs in
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
    (x.signExtend 4).setWidth w = x := by
  pbv_decide 4



/--
error: `bv_decide` found a counterexample, consider the following assignment:
  r = 8  	(m_w1 = 0xff#8)
  q = 0  	(m_w2 = 0x00#8)
  p = 7  	(m_w0 = 0x7f#8)
  x = 0x7f#7  	(x = 0x7f#8)
-/
#guard_msgs in
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (h_qp : q < p) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide 8

/--
warning: `grind` could not prove the following : p ≤ 8
---
error: unsolved goals
p r : Nat
x : BitVec p
hr : r ≤ 8
m_w1 : BitVec 8
h_m_w1 : m_w1 = Veir.Data.PBV.maskOfWidth 8 r
h_m_w1_le_blast : r ≤ 8
h_m_w1_bv_mask : m_w1 &&& m_w1 + 1#8 = 0#8
m_w0 : BitVec 8
h_m_w0 : m_w0 = Veir.Data.PBV.maskOfWidth 8 p
⊢ p ≤ 8
-/
#guard_msgs in
example (p r : Nat) (x : BitVec p) (hr : r ≤ 8) :
    x.zeroExtend r = x.zeroExtend r := by
  pbv_decide 8
  all_goals sorry

/-- Solve by first normalising and then discharging all the generated goals. -/
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (hq : q < 8) (h_qp : p < q) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_normalise 8
  bv_decide
  all_goals grind

/-- Solve by translating to the masked version and manually calling `bv_decide` -/
example (p q r : Nat) (x : BitVec p) (hr : r ≤ 8) (hq : q < 8) (h_qp : p < q) (h_pr : p < r) :
    (x.setWidth q).setWidth r = x.setWidth r := by
  pbv_decide? 8
  bv_decide
