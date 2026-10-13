import Veir.Meta.Tactic.PBVDecide

/-! ## Exercising the config options -/

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

/-- Extending, adding and truncating is the same as adding -/
example {w t : Nat} (a b : BitVec w)
  (exta extb : BitVec (t - w))
  (hqw : w ≤ t)
  (bound : t ≤ 32):
  a + b = ((exta ++ a) + (extb ++ b)).setWidth w
  := by
  pbv_decide 32 ( blastWidth := 32 )

/-! ## Goals with binders -/

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

/-! ## `BitVec` terms that are not variables -/

structure BVPair (w : Nat) where
  fst : BitVec w
  snd : BitVec w

structure ExtBV (w v : Nat) where
  val : BitVec w
  ext : BitVec v

/-- Structure projection -/
example (p q r : Nat) (a : BVPair p) (hr : r ≤ 8) (hqr : q < r) (hpq : p ≤ q) :
  (a.fst + 0) = a.fst := by
  pbv_decide 16

/-- Structure projections, related by a hypothesis -/
example (p q r : Nat) (a : BVPair p) (hr : r ≤ 8) (hqr : q < r) (hpq : p ≤ q)
  (h : a.fst = a.snd) :
  (a.fst.zeroExtend q).zeroExtend r = a.snd.zeroExtend r := by
  pbv_decide 16

/-- Function application -/
example (p q r : Nat) (f : Nat → BitVec p) (hr : r ≤ 8) (hqr : q < r) (hpq : p ≤ q) :
  ((f 0).zeroExtend q).zeroExtend r = (f 0).zeroExtend r := by
  pbv_decide 16

/-- Extending and truncating structure fields -/
example {w t v : Nat} (a : ExtBV w v)
  (hqw : w ≤ t)
  (hv : t = v + w)
  (bound : t ≤ 32) :
  (a.ext ++ a.val).setWidth w = a.val := by
  pbv_decide 16

/-- An unrelated hypothesis about a `BitVec` of another width is ignored. -/
example (z : BitVec 64) (hz : z = 0) (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 16

/-- A hypothesis whose width contains variables that appear in the goal is reverted. -/
example (p : Nat) (a b : BitVec p) (c : BitVec (p + p)) (hc : a ++ b = c) (hp : p ≤ 4)
  (x y : BitVec p) :
  x + y = y + x := by
  pbv_decide 16

/-- A `let` in the context together with a hypothesis depending on it. -/
example (p : Nat) (x : BitVec p) (hp : p ≤ 4) : True := by
  let y := x + x
  have hy : y = x + x := rfl
  have : y + 0 = x + x := by pbv_decide 16
  trivial

/-- A `let` binder in the goal. -/
example (p : Nat) (x : BitVec p) (hp : p ≤ 4) : let y := x + x; y = x + x := by
  pbv_decide 16

/-- Binders introduced from the goal keep their names, in the masks and variables. -/
example : ∀ (p : Nat) (x : BitVec p), p ≤ 4 → x + 0 = x := by
  pbv_decide 16 -bv_decide
  guard_hyp m_p
  guard_hyp x
  bv_decide

/-- `h` forces `p = 0`, since `2 mod 2^(p+1) = 0` only when `p + 1 ≤ 1`.
So every `BitVec p` is equal. -/
example (p : Nat) (x y : BitVec p) (hp : p ≤ 4)
    (h : 2#(p+1) = 0#(p+1)) : x = y := by
  pbv_decide 16

/-- An unrelated hypothesis about a `BitVec` of a literal width stays in the context,
rather than being reverted into the goal. -/
example (z : BitVec 64) (hz : z = 0) (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 16 -bv_decide
  guard_hyp hz
  bv_decide

/-- A hypothesis sharing a width variable with the goal is reverted into the goal. -/
example (p : Nat) (a b : BitVec p) (c : BitVec (p + p)) (hc : a ++ b = c) (hp : p ≤ 4)
  (x y : BitVec p) :
  x + y = y + x := by
  pbv_decide 16 -bv_decide
  fail_if_success guard_hyp hc
  bv_decide

/-- Hypotheses earlier in the context (`h1`, `h3`) only become relevant once a later
one (`h2`) adds the width `q`, so the search has to re-run when the widths grow. -/
example (p q : Nat) (a : BVPair p) (g : Nat → BitVec q)
    (h1 : g 0 = g 1) (h3 : g 1 = 0#q) (h2 : a.fst.setWidth q = g 0)
    (hq : q ≤ 8) (hp : p ≤ q) : a.fst = 0#p := by
  pbv_decide 16

/-- A width bound conjoined with a fact about a `BitVec` is still a precondition:
conjunctions are split before reverting the hypotheses mentioning `BitVec`s. -/
example (p : Nat) (x y : BitVec p) (h : p ≤ 4 ∧ x = y) : x = y := by
  pbv_decide 16
