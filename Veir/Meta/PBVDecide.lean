import Lean
import Veir.Data.PBV

open Lean Elab Tactic Meta Simp

namespace Veir.Data.PBV

def pbvTranslate (g : MVarId) (bound : Nat) : TacticM (List MVarId) := do
  logInfo s!"Deciding with bound {bound}"

-- Start by only trying to apply width elim, and generating some new hyps
-- The width_elim has type:  (o w : Nat) (Q : Prop) (h : ∀ (m : BitVec o), m = maskOfWidth o w → Q) : Q
-- so, will "feed" the current o w and goal (Q) and it will generate a new hole with the hypothesis and the Q
  let width_elim_theorem ← mkConstWithFreshMVarLevels ``width_elim
  let (g_no_w, widthName) ← g.withContext do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        if ← isDefEq ldecl.type (mkConst ``Nat) then
          logInfo m!"Applying width_elim to {ldecl.userName}"
          let applied := mkAppN width_elim_theorem #[mkNatLit bound, ldecl.toExpr, ← g.getType]
          let out ← g.apply applied
          let some out := out[0]? | throwError "Shuold have a goal here"
          -- TODO, this shuold loop over all widths
          return (out, ldecl.userName)

    throwError "haven't thought about this yet"

  let mask_name := Name.mkSimple s!"m{widthName}"
  let (_mask, g_no_w) ← g_no_w.intro mask_name
  let (mask_hyp, g_no_w) ← g_no_w.intro (Name.mkSimple s!"h_{mask_name}")

  let mut hyps := #[mask_hyp]

-- Now do var elim
  let var_elim_theorem ← mkConstWithFreshMVarLevels ``var_elim

  let (g_no_w_no_v, w_expr, new_hyps) ← g_no_w.withContext do
    let width_var ← getFVarFromUserName widthName

  -- Assert that the width variable is less than the width bound
    let width_le_bound_expr := mkAppN (Expr.const `Nat.le []) #[width_var, mkNatLit bound]
    let width_le_bound ← mkFreshExprMVar width_le_bound_expr

    let mut out_goal := g_no_w

    let mut hyps : Array FVarId := #[]

    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        -- Find the BitVec {width_expr} variables
        if ← isDefEq ldecl.type (mkApp (mkConst ``BitVec) width_var) then
          logInfo s!"Applying var_elim to {ldecl.userName}"
          let (var_hyp, goal) ← out_goal.revert #[ldecl.fvarId]
          -- not providing the `hwo` hypothesis but seems to work?
          let applied := mkAppN var_elim_theorem #[mkNatLit bound, width_var, width_le_bound]
          let out ← goal.apply applied
          let some goal := out[0]? | throwError "ahhhh"

          let some oldvar_name := var_hyp[0]? | throwError "no var name?"
          let name ← oldvar_name.getUserName
          let (_new_var, goal) ← goal.intro (name)
          let (new_hyp, goal) ← goal.intro (Name.mkSimple s!"h_m{name}")
          -- Add the mask hypothesis to the running list
          hyps := hyps.push new_hyp

          out_goal := goal
    return (out_goal, width_le_bound, hyps)

  hyps := hyps ++ new_hyps

-- Simp and push theorems
  let final_goal ← g_no_w_no_v.withContext do
    let push_th := #[``eq_iff, ``setWidth_add, ``setWidth_setWidth] -- hardcoded theorems
    let others := #[``BitVec.setWidth_eq]

    -- push theorems that need to be partially evealuted with the right
    -- symbolic width and concrete bound width
    let mut simpThms : SimpTheoremsArray := #[]
    for n in push_th do
      let push_thm ← mkAppM n #[w_expr]
      simpThms ← simpThms.addTheorem (.other n) push_thm

    -- other theorems that don't need bounds
    for n in others do
      let thm ← mkConstWithFreshMVarLevels n
      simpThms ← simpThms.addTheorem (.other n) thm

    -- the hypothesis
    for h in hyps do
      logInfo (← h.getUserName)
      let thm := mkFVar h
      simpThms ← simpThms.addTheorem (.other h.name) thm

    let ctx ← Simp.mkContext (simpTheorems := simpThms)

    let (result, _) ← simpTarget g_no_w_no_v ctx

    let some goal_out := result | throwError "solved everything?"

    return goal_out

  return [final_goal, w_expr.mvarId!]

syntax (name := pbvDecide) "pbv_decide" optConfig (ppSpace colGt num)? : tactic

@[tactic pbvDecide]
def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      replaceMainGoal (← pbvTranslate (← getMainGoal) n.getNat)
  | _ => throwUnsupportedSyntax



theorem trace_add_comm (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 13
  bv_decide
  grind
