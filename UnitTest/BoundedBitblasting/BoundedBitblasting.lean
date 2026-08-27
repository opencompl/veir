import Veir.Meta.PBVDecide

/-- Commutativity of addition -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide
  · grind

/-- Commutativity of addition with definitionally-not-syntactically equal widths-/
example (w : Nat) (x : BitVec (w + 0)) (y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide
  · grind
  · grind

/-- Commutativity of addition for three variables -/
example (w : Nat) (x y z : BitVec w) (hw : w ≤ 4) :
  x + y + z = y + x + z := by
  pbv_decide 4
  · bv_decide
  · grind

/-- Zero extending a zero extension-/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind

/-- Sign extending a zero extensions -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).signExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind

/-- Double zero extending with composite width. -/
example (p q : Nat) (x : BitVec p)
  (hr : q ≤ 8)
  (hpq : p < q) :
  (x.zeroExtend q).zeroExtend (q + q) = x.zeroExtend (q + q)
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind

/-- Appending and adding. -/
example (w : Nat) (a b : BitVec w) (hw: w ≤ 8)
  : (a ++ b) + (b ++ a) = (a ++ a) + (b ++ b)
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
