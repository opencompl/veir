module

public meta import Lean.Elab.Tactic
public meta import Veir.Meta.Tactic.PBVDecide.Main
public meta import Veir.Meta.Tactic.PBVDecide.Config

public section

namespace Veir.Meta.Tactic.PBVDecide

open Lean Elab Tactic Meta

/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a
parametric bitvector goal into a concrete width formula, and then solve it
using `bv_decide`.

Widths built out of width variables, numeric literals and `+` are supported. So
are the width relations `<`, `≤`, `>`, `≥` and `=`, and conjunctions (`∧`) of
them, when they occur as hypotheses: each is translated into the corresponding
relation on the width masks.

By default, the tactic discharged the generated main goal using `bv_decide` and
any side goals using `grind`, these prove the width parameters are bounded by
the computed bound. Options `-grind` and `-bv_decide` can be passed to turn off
either of these tactics and return the generated goals.
-/
syntax (name := pbvDecide) "pbv_decide" (ppSpace colGt num optConfig) : tactic

@[tactic pbvDecide]
public meta def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num $cfgStx:optConfig) => do
      let cfg ← elabPbvDecideConfig cfgStx
      let ctx : PbvDecideContext := { bmcBound := n.getNat, config := cfg }
      runPbvDecide (← getMainGoal) ctx
  | _ => throwUnsupportedSyntax

end Veir.Meta.Tactic.PBVDecide
