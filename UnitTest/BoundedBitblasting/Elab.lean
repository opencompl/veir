import Veir.Meta.Tactic.PBVDecide

/-- Commutativity of addition -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4 -grind
  all_goals grind

/-- Extending, adding and truncating is the same as adding -/
example {w t v: Nat} (a b : BitVec w)
  (exta extb : BitVec v)
  (hqw : w ≤ t)
  (hv : t = v + w)
  (bound : t ≤ 32):
  a + b = ((exta ++ a) + (extb ++ b)).setWidth w
  := by
  pbv_decide 16 -grind
  all_goals grind

/-- Zero extending a zero extension (≤, <) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p ≤ q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 16 -grind
  all_goals grind

/-- Commutativity of addition -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4 -bv_decide
  bv_decide

/-- Extending, adding and truncating is the same as adding -/
example {w t v: Nat} (a b : BitVec w)
  (exta extb : BitVec v)
  (hqw : w ≤ t)
  (hv : t = v + w)
  (bound : t ≤ 32):
  a + b = ((exta ++ a) + (extb ++ b)).setWidth w
  := by
  pbv_decide 16 -bv_decide
  bv_decide

/-- Zero extending a zero extension (≤, <) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p ≤ q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 16 -bv_decide
  bv_decide

/-- Commutativity of addition -/
example (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4 -bv_decide -grind
  bv_decide
  all_goals grind

/-- Extending, adding and truncating is the same as adding -/
example {w t v: Nat} (a b : BitVec w)
  (exta extb : BitVec v)
  (hqw : w ≤ t)
  (hv : t = v + w)
  (bound : t ≤ 32):
  a + b = ((exta ++ a) + (extb ++ b)).setWidth w
  := by
  pbv_decide 16 -bv_decide -grind
  bv_decide
  all_goals grind

/-- Zero extending a zero extension (≤, <) -/
example (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p ≤ q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 16 -bv_decide -grind
  bv_decide
  all_goals grind

/-! ## Goals with binders

`pbv_decide` should introduce `∀`s and implications in the goal, so that the bound
`BitVec`s and premises are visible to it.

These goals only hold if each `BitVec` is known to fit in its width (the mask
invariant introduced by `var_elim`), so they cannot be closed by treating the
lifted variables as opaque atoms.
-/

/-- `BitVec` variable bound by a `∀` in the goal -/
example (p q r : Nat) (hr : r ≤ 8) (hqr : q < r) (hpq : p ≤ q) :
  ∀ (x : BitVec p), (x.zeroExtend q).zeroExtend r = x.zeroExtend r := by
  pbv_decide 16

/-- Widths and their preconditions bound in the goal -/
example : ∀ (p q r : Nat), r ≤ 8 → q < r → p ≤ q →
  ∀ (x : BitVec p), (x.zeroExtend q).zeroExtend r = x.zeroExtend r := by
  pbv_decide 16

/-- Premise on `BitVec` variables as an implication in the goal -/
example (p q r : Nat) (x y : BitVec p) (hr : r ≤ 8) (hqr : q < r) (hpq : p ≤ q) :
  x = y → (x.zeroExtend q).zeroExtend r = y.zeroExtend r := by
  pbv_decide 16

-- /-- Widths and their preconditions bound in the goal -/
-- example : ∀ (p q r : Nat), r ≤ 8 → q < r → p ≤ q →
--   ∃ (x : BitVec p), (x.zeroExtend q).zeroExtend r = (x ^^^ 6#p).signExtend r := by
--   pbv_decide 16 -bv_decide
