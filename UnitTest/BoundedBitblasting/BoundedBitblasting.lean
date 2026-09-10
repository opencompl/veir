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

/-- Adding zero is identity -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
    x + 0 = x := by
  pbv_decide 4

/-- Adding a constant commutes -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
    x + 1 = 1 + x := by
  pbv_decide 4

/-- Adding a variable which is zero in the hypothesis is zero -/
example (w : Nat) (x y : BitVec w) (hy : y = 0) (hw : w ≤ 2) :
    x + y = x := by
  pbv_decide 4

/-- A `Nat` constant defined in the hypothesis -/
example (w n : Nat) (x : BitVec w) (hn : n = 0) (hw : w ≤ 4) :
    x + BitVec.ofNat w n = x := by
  pbv_decide 4

/-- A hypothesis links the goal to a variable that is not in the goal -/
example (w : Nat) (x z : BitVec w) (hz : z = 0) (hxz : x = z) (hw : w ≤ 4) :
    x + 1 = 1 := by
  pbv_decide 4

/-- A chain of hypotheses through two variables that are not in the goal -/
example (w : Nat) (x y z : BitVec w) (hz : z = 1) (hyz : y = z) (hxy : x = y + 1) (hw : w ≤ 4) :
    x = 2 := by
  pbv_decide 4

/-- A variable only in a hypothesis, at a width that is not in the goal -/
example (w v : Nat) (x : BitVec w) (z : BitVec v) (hz : z = 0) (hxz : x = z.setWidth w)
    (hw : w ≤ 4) (hv : v ≤ 4) :
    x + 1 = 1 := by
  pbv_decide 4

/-- Multiplying commutes -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    x * y = y * x := by
  pbv_decide 8

/-- Multiplying by one is identity -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    x * 1 = x := by
  pbv_decide 8

/-- Subtracting self equals 0 -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 4) :
    x - x = 0 := by
  pbv_decide 8

/-- Multiplication distributes over addition -/
example {w : Nat} (x y z : BitVec w) (hw : w ≤ 4) :
    x * (y + z) = x * y + x * z := by
  pbv_decide 4

/-- Subtracting and adding back is identity -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    x - y + y = x := by
  pbv_decide 8

/-- Subtraction is adding the negation -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 8) :
    x - y = x + -y := by
  pbv_decide 8

/-- Negation is an involution -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    -(-x) = x := by
  pbv_decide 8

/-- Negation commutes with multiplication -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    -(x * y) = -x * y := by
  pbv_decide 4

/-- Dividing by zero is zero -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8) :
    x / 0 = 0 := by
  pbv_decide 8

/-- Quotient and remainder reconstruct the dividend -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    x / y * y + x % y = x := by
  pbv_decide 4

/-- Taking the remainder is idempotent -/
example {w : Nat} (x y : BitVec w) (hw : w ≤ 4) :
    x % y % y = x % y := by
  pbv_decide 4

/-- Truncating a wide subtraction is subtracting the truncations -/
example {w v : Nat} (x y : BitVec v) (hw : w ≤ v) (hv : v ≤ 8) :
    (x - y).setWidth w = x.setWidth w - y.setWidth w := by
  pbv_decide 8

/-- Negation commutes with sign extension of a non-negative value -/
example {w v : Nat} (x : BitVec w) (hx : x.msb = false) (hwv : w ≤ v) (hv : v ≤ 8) :
    -(x.signExtend v) = (-x).signExtend v := by
  pbv_decide 8

/-- Shifting left appends same as appending zero -/
example {w : Nat} (x : BitVec w) (hw : w ≤ 8)
  : x <<< 1 = (x ++ 0#1).setWidth w
  := by
  pbv_decide 8
