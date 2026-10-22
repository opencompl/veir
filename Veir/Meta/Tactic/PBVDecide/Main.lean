module

public meta import Lean
public meta import Std
public import Veir.Data.PBV
public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Reify
public meta import Veir.Meta.Tactic.PBVDecide.Info
public meta import Veir.Meta.Tactic.PBVDecide.Elim
public meta import Veir.Meta.Tactic.PBVDecide.CounterExample
public meta import Veir.Meta.Tactic.PBVDecide.Push
public import Veir.Meta.Tactic.PBVDecide.PBVPushSimp

open Lean Elab Tactic Meta

namespace Veir.Meta.Tactic.PBVDecide

open Veir.Data.PBV

/--
Clear `FVar`s relating masks to the original `Nat` widths.
-/
meta def dropNatReferences (g : MVarId) (infos : WidthInfos) : MetaM MVarId := g.withContext do
  infos.infos.foldM (init := g) fun g _ info => do
    let g ← g.clear info.hypWidthLeBoundNote
    let g ← g.clear info.widthMaskHypFvar
    return g

/--
Translate the provided parametric `BitVec` goal into a concrete width goal using
the provided context. Returns the modified goal and any generate side-goals.
-/
meta def pbvTranslate (g : MVarId) (ctx : PbvDecideContext) : MetaM (MVarId × List MVarId × WidthInfos × BitVecInfos)
  := g.withContext do
  -- Construct the width environment
  let widthEnv ← createWidthEnv g
  -- Find `BitVec`s and reify their widths
  let (widthTms, bvsToRevert) ← visitExprRec { env := widthEnv } {} (← g.getType)
  -- Find `BitVec`s in the hypotheses that will be reverted along with them
  let (widthTms, bvsToRevert) ← visitDependentHyps widthTms bvsToRevert
  -- Traverse the context to find props on widths (preconditions)
  let widthProps ← reifyPreconditions widthEnv
  -- Compute the blast width
  let blastWidth := (widthTms.getWidthUpperBound ctx).max <| widthProps.getWidthUpperBound ctx
  -- Introduce the width masks, bounded by the blast width
  let (g, widthInfos) ← introMaskWidths g widthTms blastWidth ctx.bmcBound
  -- Translate props on the width vars into props on the masks
  let (g, widthInfos) ← widthProps.translateToMask g widthInfos
  -- Intro the `BitVec`s
  let (g, bvInfos) ← introMaskedBitvectors bvsToRevert g widthInfos
  -- Lift the goal to the blast width and push the `setWidth`s in
  let g ← liftToBlastWidth g blastWidth widthInfos bvInfos
  -- Drop references to `Nat` width variables
  let g ← dropNatReferences g widthInfos
  -- Run grind on subgoals
  let subgoals := widthInfos.infos.values.map (·.hypWidthLeBoundMVarId) |> .reduceOption
  return (g, subgoals, widthInfos, bvInfos)

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
meta def runGrindOnSubgoals (gs : List MVarId) : MetaM (List MVarId) := do
  return List.reduceOption <| ← gs.mapM (fun m => do
    let result ← runGrind m
    if result.isSome then
      logWarning m!"`grind` could not prove the following : {← m.getType}"
    return result)

/--
Translate the goal from a parametric multi-width goal into a concrete width goal
which can be decided using `bv_decide`. Discharge any generated goals based on
the provided context.
-/
public meta def runPbvDecide (g : MVarId) (ctx : PbvDecideContext) : TacticM Unit := do
  let (g, subgoals, widthInfos, bvInfos) ← pbvTranslate g ctx

  let subgoals ← if ctx.config.grind then runGrindOnSubgoals subgoals else pure subgoals

  if ctx.config.bv_decide then
    closeWithBvDecide g widthInfos bvInfos
    replaceMainGoal subgoals
  else
    replaceMainGoal <| g :: subgoals
    return

end Veir.Meta.Tactic.PBVDecide
