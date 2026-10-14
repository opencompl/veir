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

open Lean Elab Tactic Meta Std

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

/-- Everything found while reifying the goal and context. -/
structure Collected where
  widthTms : WidthTms
  bvs : BitVecFVarsToRevert
  props : WidthProps
  blastWidth : Nat

abbrev ContextM := ReaderT PbvDecideContext WidthEnvM

meta def collect (g : MVarId) : ContextM (Collected) := g.withContext do
  -- Find `BitVec`s and reify their widths
  let (widthTms, bvsToRevert) ← visitExprRec {} {} (← g.getType)
  -- Find `BitVec`s in the hypotheses that will be reverted along with them
  let (widthTms, bvsToRevert) ← visitDependentHyps widthTms bvsToRevert
  -- Traverse the context to find props on widths (preconditions)
  let widthProps ← reifyPreconditions
  -- Compute the blast width
  let blastWidth := (widthTms.getWidthUpperBound (← read)).max
                    <| widthProps.getWidthUpperBound (← read)

  return ({ widthTms, bvs := bvsToRevert, props := widthProps, blastWidth })

abbrev CollectedM := ReaderT (Collected × TmWidthEnv) FreshMVarM

meta def collected : CollectedM Collected := do pure (← read).fst
meta def env : CollectedM TmWidthEnv := do pure (← read).snd

meta def convertMasks (g : MVarId) : CollectedM (MVarId × Infos) := g.withContext do
  -- Introduce the width masks, bounded by the blast width
  let (g, widthInfos) ← introMaskWidths g (← collected).widthTms (← env) (← collected).blastWidth
  -- Translate props on the width vars into props on the masks
  let (g, widthInfos) ← (← collected).props.translateToMask g widthInfos
  -- Intro the `BitVec`s
  let (g, bvInfos) ← introMaskedBitvectors (← collected).bvs g widthInfos

  return (g, { width := widthInfos, bitvec := bvInfos })

abbrev InfoM := ReaderT Infos MetaM

/--
Translate the provided parametric `BitVec` goal into a concrete width goal using
the provided context. Returns the modified goal and any generate side-goals.
-/
meta def pbvTranslate (g : MVarId) (ctx : PbvDecideContext) : MetaM (MVarId × ProofObligations × Infos)
  := g.withContext do
  let (collected, env) ← ((collect g).run ctx).run {}
  -- Convert parametric widths into masks in terms of the bound
  let ((g, infos), proofs) ← ((convertMasks g).run (collected, env)).run {}
  -- Lift the goal to the blast width and push the `setWidth`s in
  let g ← liftToBlastWidth g collected.blastWidth infos.width infos.bitvec
  -- Drop references to `Nat` width variables
  let g ← dropNatReferences g infos.width

  return (g, proofs, infos)

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
meta def runGrindOnSubgoals (subgoals : ProofObligations) : MetaM (List MVarId) := do
  let result := subgoals.mvars.map (fun _prop (_expr, mvar) => do
    let result ← runGrind mvar
    if result.isSome then
      logWarning m!"`grind` could not prove the following : {← mvar.getType}"
    return result)

  return List.reduceOption <| ← result.values.mapM (·)

/--
Translate the goal from a parametric multi-width goal into a concrete width goal
which can be decided using `bv_decide`. Discharge any generated goals based on
the provided context.
-/
public meta def runPbvDecide (g : MVarId) (ctx : PbvDecideContext) : TacticM Unit := do
  let (g, subgoals, infos) ← pbvTranslate g ctx

  let subgoals ← if ctx.config.grind then runGrindOnSubgoals subgoals else pure <| subgoals.mvars.values.map (·.snd)

  if ctx.config.bv_decide then
    closeWithBvDecide g infos
    replaceMainGoal subgoals
  else
    replaceMainGoal <| g :: subgoals
    return

end Veir.Meta.Tactic.PBVDecide
