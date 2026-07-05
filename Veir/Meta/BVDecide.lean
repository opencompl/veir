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

Exception: conditional rewrites whose side condition only becomes available *after*
unfolding poison-checks into a chain of hypotheses (e.g. `isPoison_sdiv`) must go in
`veir_bv_normalize_post` instead, since only its `simp` call runs with `+contextual`
(threading those hypotheses forward as it descends). Its `discharger := bv_omega` lets
such a lemma's side condition draw on both the threaded hypotheses and any ambient
local hypotheses (e.g. a range bound on a shift amount) that aren't part of that chain,
since `bv_omega` scans the whole local context, not just the current subgoal. The
first-phase `simp` is plain (no `+contextual`, no discharger), so such lemmas silently
fail to fire there.
-/
@[expose] macro "veir_bv_normalize" : tactic =>
  `(tactic| ((
      simp -failIfUnchanged only [veir_bv_normalize] <;>
      simp +contextual -failIfUnchanged
        (discharger := bv_omega)
        only [veir_bv_normalize_post, reduceIte])))
/-
The lack of `only` is copied from the previous version of this tactic, and indeed
some of the tests seem to rely on certain simp-lemmas from the default simp-set.
We should figure out which ones, and add just those to `veir_bv_normalize_post`.
-/

/--
`veir_bv_decide` preprocesses a goal with `LLVM.Int`s and other bitblastable
Veir types into a form suitable for bitblasting, via `veir_bv_normalize`, and
then calls `bv_decide` to automatically close the goal.
-/
@[expose] macro "veir_bv_decide" : tactic =>
  `(tactic| ((veir_bv_normalize <;> bv_decide)))

attribute [veir_bv_normalize] Bool.false_eq_true false_and or_self decide_false
  dite_eq_ite Bool.if_false_right Bool.and_true implies_true
  BitVec.truncate_eq_setWidth BitVec.setWidth_eq forall_const true_and
  BitVec.natCast_eq_ofNat ge_iff_le Bool.or_false Bool.if_true_left
  BitVec.not_le Nat.sub_zero Bool.decide_or Bool.decide_eq_true
  Bool.or_eq_false_iff decide_eq_false_iff_not and_imp
  BitVec.udiv_eq

attribute [veir_bv_normalize_post] dite_eq_ite Bool.if_true_left Bool.decide_or
  Bool.decide_eq_true Bool.or_eq_false_iff decide_eq_false_iff_not
  BitVec.not_le and_imp Bool.false_eq_true implies_true Decidable.not_not
