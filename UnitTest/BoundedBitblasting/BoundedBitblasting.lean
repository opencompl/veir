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

/--
A literal in a width hypothesis that exceeds the blast width. The hypothesis
cannot be translated into a mask fact at this blast width, so it should be
ignored rather than producing an invalid `decide` proof.
-/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) (h : w < 9) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/--
Appending a bitvector of literal width as the low part. Pushing `setWidth`
through the append needs the literal width to be bounded by the blast width.
-/
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
  x ++ 0#2 = (x ++ 0#1) ++ 0#1 := by
  pbv_decide 4
  · bv_decide

/-- Equality at a literal width needs the literal to be bounded by the blast width. -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 4) :
  (x ++ 0#2).setWidth 2 = 0#2 := by
  pbv_decide 4
  · bv_decide

/--
A `BitVec` variable of literal width whose width exceeds the bound. Its width
should be treated as a literal, not as an atom bounded by the bound.
-/
example (w : Nat) (x y : BitVec w) (a b : BitVec 4) (hw : w ≤ 2) :
  x + y = y + x ∧ a + b = b + a := by
  pbv_decide 2
  · bv_decide

/-- A literal in a hypothesis equal to the blast width is still translated. -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) (h : w < 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/--
A conjunction containing a literal greater than the blast width. The whole
hypothesis is ignored; the remaining conjunct still bounds the width.
-/
example (w : Nat) (x y : BitVec w) (h : w ≤ 4 ∧ w < 9) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- A `BitVec` variable whose width is a raw natural number literal. -/
example (w : Nat) (x y : BitVec w) (a b : BitVec (nat_lit 4)) (hw : w ≤ 4) :
  x + y = y + x ∧ a + b = b + a := by
  pbv_decide 4
  · bv_decide

/-- A `BitVec` variable of width zero. -/
example (w : Nat) (x : BitVec w) (z : BitVec 0) (hw : w ≤ 4) :
  x ++ z = x ++ 0#0 := by
  pbv_decide 4
  · bv_decide

/-- The same literal width both as a variable width and in a hypothesis. -/
example (w : Nat) (x : BitVec w) (a : BitVec 4) (hw : w ≤ 4) :
  (a ++ x).setWidth w = x := by
  pbv_decide 4
  · bv_decide

/-- Sign extension to a literal width below the blast width. -/
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
  (x.signExtend 3).setWidth w = x := by
  pbv_decide 4
  · bv_decide

/--
Sign extension to a literal width equal to the blast width. The `setWidth` to
the blast width around the sign extension must not be simplified away before
the sign extension is pushed.
-/
example (w : Nat) (x : BitVec w) (hw : w ≤ 2) :
  (x.signExtend 4).setWidth w = x := by
  pbv_decide 4
  · bv_decide

/--
A hypothesis with a sum of a width and a literal on the larger side. The sum
cannot be bounded by the blast width, so the hypothesis should not introduce
an unprovable bound obligation.
-/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) (h : 1 ≤ w + 2) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/-- The same as above, with a sum of width variables. -/
example (w v : Nat) (x y : BitVec w) (hw : w ≤ 4) (hv : v ≤ 4) (h : v ≤ w + v) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide

/--
A `BitVec` variable whose width is a sum with a literal. Its width should be
reified as a sum, not treated as an atom bounded by the bound.
-/
example (w : Nat) (x y : BitVec (w + 2)) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide
