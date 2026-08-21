module

public import Veir.Data.PBV.Mask
public import Veir.Data.PBV.Push

/-! # Certificates for the directed rewriting of a reified goal.

`Veir.Data.PBV.Push` states the mathematical content of step 6 — how `setWidth o` moves past each
operation. This file restates each of those as a *certificate*: a lemma whose hypotheses are
exactly the results of rewriting the subterms, so that the tactic can build a node's proof with a
single application and never needs congruence machinery or a simp set.

Two invariants tie the recursion together, one per kind of reified term:

* a bitvector term `a` at parametric width rewrites to `a' : BitVec o` with a certificate
  `a.setWidth o = a'`;
* a proposition `P` rewrites to a `Bool` formula `b` with a certificate `P = (b = true)`.

Making the propositional side `Bool`-valued is what keeps both invariants equalities. An
implication in `Prop` is contravariant in its hypothesis, which would force the translation to run
in two directions at once; as the `Bool` operation `!h || c` the negation absorbs the flip, so
every node travels the same way and one traversal suffices. It also leaves the goal as a single
`b = true`, which is the shape `bv_decide` wants.
-/

namespace Veir.Data.PBV

public section

variable {o : Nat}

/-! ## Propositions: `P = (b = true)` -/

/-- A leaf the translation has no rule for, but which is at least decidable. -/
theorem decide_cert (P : Prop) [Decidable P] : P = (decide P = true) :=
  decide_eq_true_eq.symm

/-- Implication becomes `!h || c`, which is where the contravariance goes. -/
theorem imp_cert {h c : Prop} {h' c' : Bool}
    (fh : h = (h' = true)) (fc : c = (c' = true)) :
    (h → c) = ((!h' || c') = true) := by
  subst fh; subst fc
  cases h' <;> cases c' <;> simp

/-- A bitvector equality. -/
theorem eq_cert {w : Nat} (hw : w ≤ o) {a b : BitVec w} {a' b' : BitVec o}
    (ha : a.setWidth o = a') (hb : b.setWidth o = b') :
    (a = b) = ((a' == b') = true) := by
  subst ha; subst hb
  rw [eq_iff hw a b]
  simp

/-- A width bound becomes an unsigned bound on the corresponding masks. -/
theorem le_cert {w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂) :
    (w₁ ≤ w₂) = (m₁.ule m₂ = true) := by
  subst hm₁; subst hm₂
  rw [BitVec.ule_eq_decide_le, decide_eq_true_eq]
  exact propext (maskOfWidth_le_maskOfWidth_iff h₁ h₂).symm

/-- A strict width bound becomes a strict unsigned bound on the corresponding masks. -/
theorem lt_cert {w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂) :
    (w₁ < w₂) = (m₁.ult m₂ = true) := by
  subst hm₁; subst hm₂
  rw [BitVec.ult_eq_decide_lt, decide_eq_true_eq]
  exact propext (maskOfWidth_lt_maskOfWidth_iff h₁ h₂).symm

/-! ## Bitvectors: `a.setWidth o = a'` -/

/-- A leaf that already lives at the blast width. -/
theorem atom_cert (a : BitVec o) : a.setWidth o = a := BitVec.setWidth_eq a

/-- `BitVec.setWidth`, and hence `BitVec.zeroExtend`, which is an `abbrev` for it. -/
theorem setWidth_cert {w : Nat} (hw : w ≤ o) {u : Nat} {a : BitVec u} {a' m : BitVec o}
    (ha : a.setWidth o = a') (hm : m = maskOfWidth o w) :
    (a.setWidth w).setWidth o = a' &&& m := by
  subst ha; subst hm; exact setWidth_setWidth hw a

/-- Addition is width-sensitive, so the result is masked back down. -/
theorem add_cert {w : Nat} (hw : w ≤ o) {a b : BitVec w} {a' b' m : BitVec o}
    (ha : a.setWidth o = a') (hb : b.setWidth o = b') (hm : m = maskOfWidth o w) :
    (a + b).setWidth o = (a' + b') &&& m := by
  subst ha; subst hb; subst hm; exact setWidth_add hw a b

/-- Bitwise `and` is width-insensitive: no mask is needed, and no bound on `w`. -/
theorem and_cert {w : Nat} {a b : BitVec w} {a' b' : BitVec o}
    (ha : a.setWidth o = a') (hb : b.setWidth o = b') :
    (a &&& b).setWidth o = a' &&& b' := by
  subst ha; subst hb; exact BitVec.setWidth_and

/-! ## The sign bit -/

/-- The `Bool` certificate consumed by `signExtend_cert`.

`signBitOfMask` is unfolded in the statement, else `bv_decide` abstracts it away as an opaque
atom. It is an `@[expose] def`, so the underlying lemma still closes this by defeq. -/
theorem msb_cert {w : Nat} (hw : w ≤ o) {a : BitVec w} {a' m : BitVec o}
    (ha : a.setWidth o = a') (hm : m = maskOfWidth o w) :
    a.msb = ((a' &&& (m - (m >>> 1))) != 0#o) := by
  subst ha; subst hm; exact msb_eq_and_maskOfWidth_ne_zero hw a

/-- Sign extension fills above the source width with the sign bit, then masks to the target.
`hc` is the `Bool` certificate for the operand's sign bit. -/
theorem signExtend_cert {v t : Nat} (hv : v ≤ o) {a : BitVec v} {c : Bool}
    {a' mv mt : BitVec o}
    (ha : a.setWidth o = a') (hc : a.msb = c)
    (hmv : mv = maskOfWidth o v) (hmt : mt = maskOfWidth o t) :
    (a.signExtend t).setWidth o = (a' ||| cond c (~~~mv) 0#o) &&& mt := by
  subst ha; subst hc; subst hmv; subst hmt
  exact setWidth_signExtend_eq_and_maskOfWidth a hv
