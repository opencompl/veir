module

public import Lean

/-! ## Simpsets -/

register_simp_attr veir_bv_normalize
register_simp_attr veir_bv_normalize_post

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
      simp +contextual -failIfUnchanged [veir_bv_normalize_post, -BitVec.extractLsb_toNat])))
/- TODO: Tighten the last `simp` into a `simp only`.
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
