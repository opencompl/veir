module

public import Lean

/-! ## Simpsets -/

register_simp_attr llvm_toBitVec
register_simp_attr llvm_toBitVec_post

/-! ## LLVM Bitblasting Tactics -/

/--
`llvm_bv_decide` preprocesses a goal with `LLVM.Int`s into a form suitable
for bitblasting, using the `llvm_toBitVec` simpset followed by the
`llvm_toBitVec_post` simpset.

Note: Preprocessing lemmas should almost always be added to `llvm_toBitVec`.
Preprocessing happens in two stages because rewrites are generally
easier to state with the dependently-typed `Int.getValue`, but `bv_decide` works
better with the non-dependent `Int.getValueD`. Thus, `llvm_toBitVec_post`
contains `Int.getValue_eq_getValueD`, which rewrites the former into the latter.
-/
@[expose] macro "llvm_bv_normalize" : tactic =>
  `(tactic| ((
      simp -failIfUnchanged only [llvm_toBitVec] <;>
      simp -failIfUnchanged [llvm_toBitVec_post])))
/- TODO: Tighten the last `simp` into a `simp only`.
The lack of `only` is copied from the previous version of this tactic, and indeed
some of the tests seem to rely on certain simp-lemmas from the default simp-set.
We should figure out which ones, and add just those to `llvm_toBitVec_post`.
-/

/--
`llvm_bv_decide` preprocesses a goal with `LLVM.Int`s into a form suitable
for bitblasting, via `llvm_bv_normalize`, and then calls `bv_decide` to
automatically close the goal.
-/
@[expose] macro "llvm_bv_decide" : tactic =>
  `(tactic| ((llvm_bv_normalize <;> bv_decide)))
