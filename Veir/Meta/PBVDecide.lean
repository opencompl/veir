import Lean
import Veir.Data.PBV

open Lean Elab Tactic Meta

namespace Veir.Data.PBV

-- Start by only trying to apply width elim, and generating some new hyps
-- The width_elim has type:  (o w : Nat) (Q : Prop) (h : ∀ (m : BitVec o), m = maskOfWidth o w → Q) : Q
-- so, will "feed" the current o w and goal (Q) and it will generate a new hole with the hypothesis and the Q
def pbvTranslate (g : MVarId) (bound : Nat) : TacticM MVarId := do
  logInfo ("Deciding with bound")
  let width_elim_theorem ← mkConstWithFreshMVarLevels ``width_elim
  let out ← g.withContext do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        if ← isDefEq ldecl.type (mkConst ``Nat) then
          logInfo m!"Found a var! {ldecl.userName}"
          let applied := mkAppN width_elim_theorem #[mkNatLit bound, ldecl.toExpr, ← g.getType]
          return ← g.apply applied
    throwError "haven't thought about this yet"

  let some new_g := out[0]? | throwError "Shuold have a goal here"

  logInfo (toString width_elim_theorem)
  return new_g


syntax (name := pbvDecide) "pbv_decide" optConfig (ppSpace colGt num)? : tactic

@[tactic pbvDecide]
def evalPbvDecide : Tactic := fun stx => do
  let out ← pbvTranslate (← getMainGoal) stx[0].toNat
  replaceMainGoal [out]



theorem trace_add_comm (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 9
