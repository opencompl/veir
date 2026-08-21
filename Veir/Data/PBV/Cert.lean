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
* a predicate `P` rewrites to `P'` with a certificate `P' → P`, the direction that lets the
  translated goal discharge the original.

The predicate direction is an implication rather than an equality on purpose. Hypotheses are
reverted into the goal before reification, so `imp_cert` translates them covariantly and the
conclusion contravariantly; asking for an equality would mean proving a converse for every width
predicate, and `mask_lt_mask` only runs one way.
-/

namespace Veir.Data.PBV

public section

variable {o : Nat}

/-! ## Predicates: `P' → P` -/

/-- Implication is contravariant in its hypothesis: to translate `h → c` it is the *hypothesis*
that travels forwards and the conclusion that travels backwards. -/
theorem imp_cert {h h' c c' : Prop} (fh : h → h') (fc : c' → c) : (h' → c') → (h → c) :=
  fun k hh => fc (k (fh hh))

/-- A bitvector equality in conclusion position. -/
theorem eq_cert {w : Nat} (hw : w ≤ o) {a b : BitVec w} {a' b' : BitVec o}
    (ha : a.setWidth o = a') (hb : b.setWidth o = b') : (a' = b') → (a = b) := by
  subst ha; subst hb
  exact fun h => BitVec.setWidth_inj hw h

/-- A bitvector equality in hypothesis position, where the translation runs forwards. -/
theorem eq_cert_fwd {w : Nat} {a b : BitVec w} {a' b' : BitVec o}
    (ha : a.setWidth o = a') (hb : b.setWidth o = b') : (a = b) → (a' = b') := by
  subst ha; subst hb
  exact fun h => congrArg _ h

/-- A width bound becomes a bound on the corresponding masks. -/
theorem le_cert {w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂) :
    (w₁ ≤ w₂) → (m₁ ≤ m₂) :=
  fun hw => mask_le_mask h₁ h₂ hm₁ hm₂ hw

/-- A strict width bound becomes a strict bound on the corresponding masks. -/
theorem lt_cert {w₁ w₂ : Nat} {m₁ m₂ : BitVec o} (h₁ : w₁ ≤ o) (h₂ : w₂ ≤ o)
    (hm₁ : m₁ = maskOfWidth o w₁) (hm₂ : m₂ = maskOfWidth o w₂) :
    (w₁ < w₂) → (m₁ < m₂) :=
  fun hw => mask_lt_mask h₁ h₂ hm₁ hm₂ hw

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
`hc` is the `Bool` certificate for the operand's sign bit; it is the only place the reified
language's `bool` kind is consumed. -/
theorem signExtend_cert {v t : Nat} (hv : v ≤ o) {a : BitVec v} {c : Bool}
    {a' mv mt : BitVec o}
    (ha : a.setWidth o = a') (hc : a.msb = c)
    (hmv : mv = maskOfWidth o v) (hmt : mt = maskOfWidth o t) :
    (a.signExtend t).setWidth o = (a' ||| cond c (~~~mv) 0#o) &&& mt := by
  subst ha; subst hc; subst hmv; subst hmt
  exact setWidth_signExtend_eq_and_maskOfWidth a hv
