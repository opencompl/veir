module

public meta import Lean
public meta import Std
public import Veir.Data.PBV
public import Lean.Meta.Tactic.BVDecide.Main
public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Reify
public meta import Veir.Meta.Tactic.PBVDecide.WidthInfo
public meta import Veir.Meta.Tactic.PBVDecide.BitVecInfo
public meta import Veir.Meta.Tactic.PBVDecide.CounterExample
public import Veir.Meta.Tactic.PBVDecide.PBVPushSimp

open Lean Elab Tactic Meta Simp Std Tactic.BVDecide

namespace Veir.Meta.Tactic.PBVDecide

open Veir.Data.PBV

/--
Add `eq_iff` with the blast width pre-filled, which lifts equalities to the
blast width by wrapping both sides in a `setWidth`.
-/
meta def addEqIff (g : MVarId) (blastWidth : Nat) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let liftThms ← labelled `pbv_lift
  liftThms.foldlM (init := simp) fun simp name => do
    simp.addTheorem (.other name) <| ← mkAppM name #[mkNatLit blastWidth]

/--
Add theorems to the Simp theorem context that push the `setWidth`s in.
-/
meta def addPushTheorems (g : MVarId) (blastWidth : Nat) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  -- Push theorems which require specifying the blastWidth explicitly.
  let simp ← (← labelled `pbv_push_bound).foldlM (init := simp) fun simps name => do
    return ← simps.addTheorem (.other name) (← mkAppM name #[mkNatLit blastWidth])
  -- Push theorems.
  let some pushExt ← getSimpExtension? `pbv_push
    | throwError "Failed to obtain `pbv_push simp set."

  return simp.push <| ← pushExt.getTheorems

/--
Add the mask hypotheses of the translated `BitVec`s to the Simp theorem context.
These simplify the final formula by removing redundant masking operations; they
are not strictly necessary for `bv_decide` to decide the resulting formula.
-/
meta def addBvInfos (g : MVarId) (bvInfos : BitVecInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for info in bvInfos.infos do
      simp ← simp.addTheorem (.other info.bvHyp.name) (mkFVar info.bvHyp)
  return simp

/--
Add the hypotheses bounding each width by the blast width to the simp set.
-/
meta def addWidthInfosSimpLemmas (g : MVarId) (widthInfos : WidthInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for (_wexpr, widthInfo) in widthInfos.infos do
    simp ← simp.addTheorem (.other widthInfo.hypWidthLeBoundNote.name)
        (mkFVar widthInfo.hypWidthLeBoundNote)
    simp ← simp.addTheorem (.other widthInfo.widthMaskHypFvar.name)
      (← mkEqSymm <| .fvar widthInfo.widthMaskHypFvar)
  return simp

/--
Run simp on an MVarId given a set of simp theorems.
Throws if `simp` closes the goal outright.
-/
meta def applySimp (g : MVarId) (simp : SimpTheoremsArray)
    (config : Simp.Config := { decide := false }) : MetaM MVarId := g.withContext do
  let simpCtx ← Simp.mkContext (config := config) (simpTheorems := simp)
  let (some g, _) ← g.withContext do simpTarget g simpCtx
    | throwError "goal solved by simp"
  return g

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
  let (g, widthTms, bvsToRevert) ← visitExprRec g { env := widthEnv } {} (← g.getType)
  -- Find `BitVec`s in the hypotheses that will be reverted along with them
  let (g, widthTms, bvsToRevert) ← visitDependentHyps g widthTms bvsToRevert
  -- Traverse the context to find props on widths (preconditions)
  let widthProps ← reifyPreconditions widthEnv
  -- Compute the blast width
  let blastWidth := (widthTms.getWidthUpperBound ctx).max <| widthProps.getWidthUpperBound ctx
  -- Introduce the width masks, bounded by the blast width
  let (g, widthInfos) ← introMaskWidths g widthTms blastWidth
  -- Translate props on the width vars into props on the masks
  let (g, widthInfos) ← widthProps.translateToMask g widthInfos
  -- Intro the `BitVec`s
  let (g, bvInfos) ← introMaskedBitvectors bvsToRevert g widthInfos
  -- Lift equalities to the blast width. A single pass applies `eq_iff` once:
  -- otherwise the lifted equality, now at the blast width, gets lifted again.
  let eqThms ← addEqIff g blastWidth <| ← addWidthInfosSimpLemmas g widthInfos #[]
  let g ← applySimp g eqThms { decide := false, singlePass := true }
  -- Create simp set to push the `setWidth`s in
  let thms := ← addPushTheorems g blastWidth
           <| ← addBvInfos g bvInfos
           <| ← addWidthInfosSimpLemmas g widthInfos #[]
  -- Run simp
  let g ← applySimp g thms
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
