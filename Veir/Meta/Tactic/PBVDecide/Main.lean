module

public meta import Lean
public meta import Std
public import Veir.Data.PBV
public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Reify
public meta import Veir.Meta.Tactic.PBVDecide.Elim
public meta import Veir.Meta.Tactic.PBVDecide.CounterExample
public meta import Veir.Meta.Tactic.PBVDecide.Push
public import Veir.Meta.Tactic.PBVDecide.PBVPushSimp

open Lean Elab Tactic Meta Std

namespace Veir.Meta.Tactic.PBVDecide

open Veir.Data.PBV

/--
Clear `FVar`s relating masks to the original `Nat` widths.
-/
meta def dropNatReferences (g : MVarId) : TranslateM MVarId := g.withContext do
  (← get).widthInfos.foldM (init := g) fun g _ info => do
    let g ← g.clear info.hypWidthLeBoundNote
    let g ← g.clear info.widthMaskHypFvar
    return g

/--
Translate the provided parametric `BitVec` goal into a concrete width goal using
the provided context. Returns the modified goal and any generate side-goals.
-/
meta def pbvTranslate (g : MVarId) : TranslateM MVarId := g.withContext do
  -- Introduce the width masks, bounded by the blast width
  let g ← introMaskWidths g
  -- Translate props on the width vars into props on the masks
  let g ← translatePropsToMask g
  -- Intro the `BitVec`s
  let g ← introMaskedBitvectors g
  -- Lift the goal to the blast width and push the `setWidth`s in
  let g ← liftToBlastWidth g
  -- Drop references to `Nat` width variables
  let g ← dropNatReferences g
  return g

/--
Helper to run grind on a given `MVarId`. If `grind` could not prove the goal
the original goal state is restored and returned.
-/
meta def runGrind (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let s ← saveState
  try
    let result ← Grind.main g <| ← Grind.mkDefaultParams {}
    if result.hasFailed then
      s.restore
      return some g
    else
      return none
  catch _ =>
    s.restore
    return some g

/--
Run `grind` on a list of `MVarId`s, warning if any were not discharged.
-/
meta def runGrindOnSubgoals (subgoals : List MVarId) : MetaM (List MVarId) := do
  let result := subgoals.map (fun mvar => do
    let result ← runGrind mvar
    if result.isSome then
      logWarning m!"`grind` could not prove the following : {← mvar.getType}"
    return result)

  return List.reduceOption <| ← result.mapM (·)

/--
Translate the goal from a parametric multi-width goal into a concrete width goal
which can be decided using `bv_decide`. Discharge any generated goals based on
the provided context.
-/
public meta def runPbvDecide (g : MVarId) (ctx : PbvDecideContext) : TacticM Unit := do
  let (blastWidth, reifiedState) ← ReifyM.run ctx <| reifyWidths g
  let (g, translated) ← TranslateM.run { reifiedState with blastWidth } <| pbvTranslate g

  let subgoals ← if ctx.config.grind
                then runGrindOnSubgoals translated.subgoals
                else pure translated.subgoals

  if ctx.config.bv_decide then
    closeWithBvDecide g translated
    replaceMainGoal subgoals
  else
    replaceMainGoal <| g :: subgoals
    return

end Veir.Meta.Tactic.PBVDecide
