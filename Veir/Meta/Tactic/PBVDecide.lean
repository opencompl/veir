module

public import Veir.Meta.Tactic.PBVDecide.PBVDecide
public import Veir.Meta.Tactic.BVDecide

/-! The `pbv_decide` tactic. See `Veir.Data.PBV` for the technique it implements. -/

/--
`veir_pbv_decide n` preprocesses a goal with `LLVM.Int`s and other bitblastable
Veir types via `veir_bv_normalize`, and then calls `pbv_decide n` to close the
goal for every width up to `n`. Any configuration options (e.g.
`(blastWidth := 64)`) are passed through to `pbv_decide`.
-/
@[expose] macro "veir_pbv_decide" ppSpace colGt n:num cfg:optConfig : tactic =>
  `(tactic| ((veir_bv_normalize <;> pbv_decide $n $cfg)))
