module

public import Veir.Meta.BVNormalizeSimp

/-! ## Veir Bitblasting Tactic -/

/--
`veir_bv_normalize` preprocesses a goal with `LLVM.Int`s and other bitblastable
Veir types into a form suitable for bitblasting, using the `veir_bv_normalize`
simpset followed by the `veir_bv_normalize_post` simpset.

Note: Preprocessing lemmas should almost always be added to `veir_bv_normalize`.
Preprocessing happens in two stages because rewrites are generally
easier to state with the dependently-typed `Int.getValue`, but `bv_decide` works
better with the non-dependent `Int.getValueD`. Thus, `veir_bv_normalize_post`
contains `Int.getValue_eq_getValueD`, which rewrites the former into the latter.
-/
@[expose] macro "veir_bv_normalize" : tactic =>
  `(tactic| ((
      simp -failIfUnchanged only [veir_bv_normalize] <;>
      simp +contextual -failIfUnchanged only [veir_bv_normalize_post])))
/-
The lack of `only` is copied from the previous version of this tactic, and indeed
some of the tests seem to rely on certain simp-lemmas from the default simp-set.
We should figure out which ones, and add just those to `veir_bv_normalize_post`.
-/

/--
`veir_bv_decide` preprocesses a goal with `LLVM.Int`s and other bitblastable
Veir types into a form suitable for bitblasting, via `veir_bv_normalize`, and
then calls `bv_decide` to automatically close the goal. Accepts the same
configuration syntax as `bv_decide` itself, e.g. `veir_bv_decide (config := {
timeout := 120 })`.
-/
@[expose] macro "veir_bv_decide" cfg:Lean.Parser.Tactic.optConfig : tactic =>
  `(tactic| ((veir_bv_normalize <;> bv_decide $cfg)))

attribute [veir_bv_normalize] Bool.false_eq_true false_and or_self decide_false
  dite_eq_ite Bool.if_false_right Bool.and_true implies_true
  BitVec.truncate_eq_setWidth BitVec.setWidth_eq forall_const true_and
  BitVec.natCast_eq_ofNat ge_iff_le Bool.or_false Bool.if_true_left
  BitVec.not_le Nat.sub_zero Bool.decide_or Bool.decide_eq_true
  Bool.or_eq_false_iff decide_eq_false_iff_not and_imp

attribute [veir_bv_normalize_post] dite_eq_ite Bool.if_true_left Bool.decide_or
  Bool.decide_eq_true Bool.or_eq_false_iff decide_eq_false_iff_not
  BitVec.not_le and_imp
