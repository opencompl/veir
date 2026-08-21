import Veir.Meta.PBVDecide

example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 13
  · bv_decide
  · grind

example (w : Nat) (x y z : BitVec w) (hw : w ≤ 4) :
  x + y + z = y + x + z := by
  pbv_decide 13
  · bv_decide
  · grind

example (w : Nat) (x : BitVec (w + 0)) (y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 13
  · bv_decide
  · grind

-- Zero extension through an intermediate parametric width.
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind

-- Sign extending a zero extension: the sign bit is known to be clear because `p < q`.
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).signExtend r = x.zeroExtend r := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind
