module

public meta import Lean
public import Veir.Meta.Tactic.PBVDecide.PBVPushSimp
public meta import Veir.Meta.Tactic.PBVDecide.Basic

open Lean Meta

namespace Veir.Meta.Tactic.PBVDecide

/--
Add `pbv_lift` theorems with the blast width pre-filled, which lifts equalities
to the blast width by wrapping both sides in a `setWidth`.
-/
meta def addLiftThms (g : MVarId) (blastWidth : Nat) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let liftThms ← labelled `pbv_lift
  liftThms.foldlM (init := simp) fun simp name => do
    simp.addTheorem (.other name) <| ← mkAppM name #[mkNatLit blastWidth]

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
meta def addBvInfos (g : MVarId) (simp : SimpTheoremsArray) : TranslateM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for info in (← get).bitvecInfos do
      simp ← simp.addTheorem (.other info.bvHyp.name) (mkFVar info.bvHyp)
  return simp

/--
Add the hypotheses bounding each width by the blast width to the simp set.
-/
meta def addWidthInfosSimpLemmas (g : MVarId) (simp : SimpTheoremsArray) : TranslateM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for (_wexpr, widthInfo) in (← get).widthInfos do
    simp ← simp.addTheorem (.other widthInfo.hypWidthLeBoundNote.name)
        (mkFVar widthInfo.hypWidthLeBoundNote)
    simp ← simp.addTheorem (.other widthInfo.widthMaskHypFvar.name)
      (← mkEqSymm <| .fvar widthInfo.widthMaskHypFvar)
  return simp

/--
Throws if `simp` closes the goal outright.
-/
meta def applySimp (g : MVarId) (simp : SimpTheoremsArray)
    (config : Simp.Config := { decide := false }) : MetaM MVarId := g.withContext do
  let simpCtx ← Simp.mkContext (config := config) (simpTheorems := simp)
  let (some g, _) ← simpTarget g simpCtx
    | throwError "goal solved by simp"
  return g

/--
Lift the goal to the blast width, then push the resulting `setWidth`s in so
that `bv_decide` can decide it.
-/
public meta def liftToBlastWidth (g : MVarId) : TranslateM MVarId := g.withContext do
  -- Lift equalities to the blast width. A single pass applies the `pbv_lift`
  -- theorems once: otherwise the lifted equality, now at the blast width, gets
  -- lifted again.
  let eqThms ← addLiftThms g (← read).blastWidth <| ← addWidthInfosSimpLemmas g #[]
  let g ← applySimp g eqThms { decide := false, singlePass := true }
  -- Create simp set to push the `setWidth`s in
  let thms := ← addPushTheorems g (← read).blastWidth
           <| ← addBvInfos g
           <| ← addWidthInfosSimpLemmas g #[]
  -- Run simp
  applySimp g thms

end Veir.Meta.Tactic.PBVDecide
