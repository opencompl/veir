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

open Veir.Data.PBV

theorem t1 (o : Nat) {a : BitVec o} (h : w2 ≤ w1)
  : a &&& maskOfWidth o w1 &&& maskOfWidth o w2 = a &&& maskOfWidth o w2 := by sorry
theorem t2 (o : Nat) {a b : BitVec o} (h : w1 ≤ w2)
  : ((a &&& (maskOfWidth o w2)) * (b &&& (maskOfWidth o w2))) &&& (maskOfWidth o w1) = ((a &&& (maskOfWidth o w1)) * (b &&& (maskOfWidth o w1))) &&& (maskOfWidth o w1) := by sorry
theorem t3 (o : Nat) {a b : BitVec o} (h : w2 ≤ w1)
  : (a ||| (b &&& (maskOfWidth o w1))) &&& (maskOfWidth o w2) = ((a &&& (maskOfWidth o w2)) ||| (b &&& (maskOfWidth o w2))) &&& (maskOfWidth o w2) := by sorry
theorem t5 (o : Nat) {a : BitVec o} (h : w2 ≤ w1)
  : (a <<< (maskOfWidth o w1).cpop) &&& maskOfWidth o w2 = 0 := by sorry
-- theorem t4 (a b m1 m2 : BitVec o) (h : m1 ≤ m2)
--   : ((a &&& m2) <<< b) &&& m1 = ((a &&& m1) <<< b) &&& m1 := by sorry
-- theorem t3 (a b m : BitVec o) : (a ||| b) &&& m = ((a &&& m) ||| (b &&& m)) &&& m := by sorry
-- theorem t4 (a b m : BitVec o) : (a <<< b) &&& m = ((a &&& m) <<< (b &&& m)) &&& m := by sorry

-- theorem t6 (a b ma mb mc : BitVec o) (h : mc ≤ mb) : ((a &&& ma) <<< mb.cpop ||| (b &&& mb)) &&& mc = b &&& mc := by sorry
theorem t6 (o : Nat) (b : BitVec o) : 0 ||| b = b := by simp

open Lean Elab Tactic in
/-- Run `tac` and report how many heartbeats it used (same units as `maxHeartbeats`). -/
elab "hb " tac:tacticSeq : tactic => do
  let start ← IO.getNumHeartbeats
  try evalTactic tac
  finally
    let used := (← IO.getNumHeartbeats) - start
    logInfo m!"{used / 1000} heartbeats"

example {w t : Nat} (a b : BitVec w) (exta extb : BitVec (t - w)) (hqw : w ≤ t)
    (bound : t ≤ 16) :
    a * b = ((exta ++ a) * (extb ++ b)).setWidth w := by
  pbv_decide 64 (blastWidth := 16) -bv_decide
  simp only [h_m_t_sub_w_add_w, h_m_w, h_m_t, h_m_t_sub_w]
  hb simp (disch := omega) only [t1 16, t2 16, t3 16, t6, t5 16]
