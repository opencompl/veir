module

public meta import Lean
public import Veir.PatternRewriter.Puddle.CTreeValidity

namespace Veir.Puddle.CTree

public section

open Lean Elab Tactic in
/-- Discharge the structural CTree validity obligations, leaving semantic preservation. -/
elab "simpPuddleValid" : tactic => withMainContext do
  unless (← getMainTarget).isAppOf ``Pattern.Valid do
    throwError "expected a CTree pattern validity goal"
  evalTactic (← `(tactic| (
    unfoldPuddleBuilder
    constructor
    · simp [Pattern.Supported, get_effects, is_terminator]
    · cbv
    · open scoped Veir.Puddle.PuddleCbv in cbv)))

end

end Veir.Puddle.CTree
