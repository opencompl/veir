import Veir.Meta.PBVDecide

/-- Commutativity of addition -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- Commutativity of addition with definitionally-not-syntactically equal widths -/
example (w : Nat) (x : BitVec (w + 0)) (y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- Commutativity of addition for three variables -/
example (w : Nat) (x y z : BitVec w) (hw : w ≤ 4) :
  x + y + z = y + x + z := by
  pbv_decide 4
  · bv_decide

/-- Appending and adding -/
example (w : Nat) (a b : BitVec w) (hw : w ≤ 8) :
  (a ++ b) + (b ++ a) = (a ++ a) + (b ++ b) := by
  pbv_decide 8
  · bv_decide

/-- Extending, adding and truncating is the same as adding -/
example {w t v: Nat} (a b : BitVec w)
  (exta extb : BitVec v)
  (hqw : w ≤ t)
  (hv : t = v + w)
  (bound : t ≤ 32):
  a + b = ((exta ++ a) + (extb ++ b)).setWidth w
  := by
  pbv_decide 16
  · bv_decide

/-- Zero extending a zero extension (≤, <) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p ≤ q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide

/-- Zero extending a zero extension (≥, >) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : r > q)
  (hpq : q ≥ p) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide

/-- Double zero extending with conjunction condition -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (h : q < r ∧ p < q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide

/-- Double zero extending with composite width -/
example (p q : Nat) (x : BitVec p)
  (hq : q ≤ 8)
  (hqp : q > p) :
  (x.zeroExtend q).zeroExtend (q + q) = x.zeroExtend (q + q)
  := by
  pbv_decide 8
  · bv_decide

/-- Sign extending a sign extension -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q ≤ r)
  (hpq : p ≤ q) :
  (x.signExtend q).signExtend r = x.signExtend r
  := by
  pbv_decide 8
  · bv_decide

/-- Sign extending a zero extension -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).signExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide

/-- Resizing preserves the msb iff the width is unchanged -/
example (p w : Nat) (x : BitVec p)
  (hp : p ≤ 8)
  (hwp : w = p) :
  (x.setWidth w).msb = x.msb
  := by
  pbv_decide 8
  · bv_decide

/-- A goal width defined by a sum only mentioned in a hypothesis (`=`). -/
example (w v t : Nat) (x : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (ht : t = w + v) :
  (x.zeroExtend t).setWidth w = x := by
  pbv_decide 4
  · bv_decide

/-- Nested sum in a hypothesis requires a blast width of three times the bound. -/
example (u v w t : Nat) (x : BitVec w) (hu : u ≤ 4) (hv : v ≤ 4) (hw : w ≤ 4)
  (ht : t = u + v + w) :
  (x.zeroExtend t).setWidth w = x := by
  pbv_decide 4
  · bv_decide

/-- Sum in a hypothesis larger than any sum in the goal. -/
example (w v : Nat) (a b : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w + w ≤ w + w + v) :
  (a ++ b) + (b ++ a) = (a ++ a) + (b ++ b) := by
  pbv_decide 4
  · bv_decide

/-- Sums in a hypothesis under a conjunction contribute to the blast width. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w ≤ w + v ∧ v ≤ w + v) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- Sums in a hypothesis using `≥` contribute to the blast width. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w + v ≥ v) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- Sums on both sides of a `<` hypothesis contribute to the blast width. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : w + w < w + v) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- Appending to a bitvector of literal width -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 10) :
  0#4 ++ x = x.zeroExtend (4 + w) := by
  pbv_decide 10
  · bv_decide

/-- Zero-extending by a literal amount preserves the value -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 8) :
  (x.zeroExtend (w + 2)).setWidth w = x := by
  pbv_decide 8
  · bv_decide
