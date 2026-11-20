module

public meta import Lean.Elab.Tactic

/-! ## Proof markers

Identity theorems that veir's tactics wrap around the proofs they close, so that how a theorem
is proven can be read from its proof term (by tools counting veir's proofs) rather than from its
source text. A marker does not change what the kernel checks: `closedByBvNormalize h` is `h`.
-/

public section

namespace Veir.Meta.Tactic

/-- Marks a proof that `veir_bv_normalize` closed on its own. -/
theorem closedByBvNormalize {p : Prop} (h : p) : p := h

/-- Marks a proof closed by `pbv_decide`, including when it closes the goal by unfolding the
derived operations, before applying `Veir.Data.PBV.width_elim`. -/
theorem provedByPbvDecide {p : Prop} (h : p) : p := h

open Lean Elab Tactic Meta in
/-- Runs `k` on a fresh copy of the main goal, in its local context. If `k` closes it, the main
goal is assigned `marker _ proof`; otherwise the proof is passed through unmarked, and the goals
`k` left become the goals. -/
meta def markIfClosed (marker : Name) (k : TacticM Unit) : TacticM Unit := do
  let g ← getMainGoal
  let type ← g.getType
  let copy ← g.withContext <| mkFreshExprSyntheticOpaqueMVar type (← g.getTag)
  setGoals [copy.mvarId!]
  k
  let rest ← getUnsolvedGoals
  g.assign (if rest.isEmpty then mkApp2 (mkConst marker) type copy else copy)
  setGoals rest

open Lean Elab Tactic in
/-- `veir_mark_normalized tac` runs `tac`, and marks the proof with `closedByBvNormalize` if `tac`
closed the goal. -/
elab "veir_mark_normalized " tac:tactic : tactic =>
  markIfClosed ``closedByBvNormalize (evalTactic tac)

end Veir.Meta.Tactic
