module

public meta import Lean
public meta import Std
public import Lean.Meta.Tactic.BVDecide.Main
public meta import Veir.Meta.Tactic.PBVDecide.Reify
public meta import Veir.Meta.Tactic.PBVDecide.Info

open Lean Elab Tactic Meta Std Tactic.BVDecide

namespace Veir.Meta.Tactic.PBVDecide

meta structure WidthMaskCex where
  /-- Original counterexample. -/
  counterExample : Expr × BVExpr.PackedBitVec
  /-- Width expression the mask encodes. -/
  widthNatExpr : Expr
  /-- User facing name of the mask. -/
  name : Name

/-- Value of the width, derived from the bitvector. -/
meta def WidthMaskCex.val (self : WidthMaskCex) : Nat :=
  BitVec.cpop self.counterExample.snd.bv |> BitVec.toNat

abbrev WidthMaskCexs := HashMap WidthTm WidthMaskCex

meta instance : ToMessageData WidthMaskCex where
  toMessageData f := m!"{f.widthNatExpr} = {f.val}  \t({f.name} = {f.counterExample.snd.bv})"

meta structure BitVecCex where
  /-- Original counterexample. -/
  counterExample : Expr × BVExpr.PackedBitVec
  /-- Corresponding concrete width. -/
  width : WidthMaskCex
  /-- User facing variable name. -/
  name : Name

/-- Concrete value in terms of the concrete width. -/
meta def BitVecCex.assignedVal (self : BitVecCex) : BitVec self.width.val :=
  self.counterExample.snd.bv.setWidth self.width.val

abbrev BitVecCexs := Array BitVecCex

meta instance : ToMessageData BitVecCex where
  toMessageData f := m!"{f.name} = {f.assignedVal}"

meta def findFVarIdInCounterExample? (cex : CounterExample) (id : FVarId) : Option (Expr × BVExpr.PackedBitVec) :=
  cex.equations.find? (fun (e, _) => Id.run do
    let some fvar := Expr.fvarId? e | return false
    return fvar == id
  )

/--
Find masks in the counterexamples and convert them into `Nat` widths to display
in the error message. Warn if any masks were not assigned a value.
-/
meta def getWidthCounterExamples (widthInfos : WidthInfos) (counterExample : CounterExample) : MetaM WidthMaskCexs := do
  let mut widthMaskCexs : WidthMaskCexs := {}

  for (widthTm, winfo) in widthInfos.infos do
    let name ← widthTm.toName
    let originalNatWidth := widthTm.toExpr widthInfos.env
    match findFVarIdInCounterExample? counterExample winfo.widthMaskFVar with
    | some (eq, bv) => do
      -- Check that the mask is a mask.
      let isMask := bv.bv &&& (bv.bv + 1)
      if isMask != 0#bv.w then
        throwError m!"Generated counterexample for mask {name} ({originalNatWidth}) is not a mask. \
                        {bv.bv}, {name} &&& {name} + 1 = {isMask} != 0."

      let username ← counterExample.goal.withContext do eq.fvarId!.getUserName
      widthMaskCexs := widthMaskCexs.insert widthTm {
          counterExample := (eq, bv),
          widthNatExpr := originalNatWidth,
          name := username,
      }
    | none =>
      logWarning m!"No assignment found in the counterexample for mask {name} of width {originalNatWidth}."

  return widthMaskCexs

/--
Find bitvecs in the counterexamples and convert them to their corresponding width.
-/
meta def getBitVecCounterExamples (bvInfos : BitVecInfos) (widthCexs: WidthMaskCexs)
    (counterExample : CounterExample) : MetaM BitVecCexs := do
  bvInfos.infos.mapM (fun bvinfo => counterExample.goal.withContext do
    let name ← bvinfo.bvVar.getUserName
    match findFVarIdInCounterExample? counterExample bvinfo.bvVar with
    | some (eq, bv) => do
      let some widthCex := widthCexs[bvinfo.bvWidthTm]?
        | throwError m!"Width ({← bvinfo.bvWidthTm.toName}) of BitVec {name} is missing from the generated counterexamples."
      return {counterExample := (eq, bv), width := widthCex, name}
    | none =>
      throwError m!"No counterexample generated for BitVec {name}"
  )

/--
Convert a bv_decide counterexample into a string, mapping concrete mask `BitVec`
values to concrete width `Nat` values, and keeping track if any counterexamples
belong to expressions which have been abstracted as opaque variables, or if any
widths were abstracted as atoms independent of the other widths.
-/
meta def prettyPrintCounterExample (counterExample : CounterExample) (widthInfos : WidthInfos)
    (bvInfos : BitVecInfos) : MetaM MessageData := do
  let widthCexs ← getWidthCounterExamples widthInfos counterExample
  let bitvecCexs ← getBitVecCounterExamples bvInfos widthCexs counterExample

  let visitedExamples : HashSet Expr := widthCexs.fold (fun acc _ cex => acc.insert cex.counterExample.fst)
                                     <| bitvecCexs.foldl (fun acc cex => acc.insert cex.counterExample.fst) {}

  let opaqueVariables : Array MessageData ← counterExample.equations.filterMapM
    (fun (eq, bv) => counterExample.goal.withContext do
      if !visitedExamples.contains eq then
        return m!"{eq} = {bv.bv}"
      else
        return none
    )

  -- Widths that are neither variables, literals nor sums are atoms whose masks
  -- are unrelated to the masks of the other widths.
  let opaqueWidths : Array Expr :=
    widthInfos.infos.keys.filterMap (fun | .widthAtom id => some id | _ => none)
      |>.toArray.qsort (· < ·) |>.map (widthInfos.env.width2expr[·]!)

  let mut err := m!""
  if opaqueVariables.isEmpty && opaqueWidths.isEmpty then
    err := err ++ "`pbv_decide` found a counterexample, consider the following assignment:\n"
  else
    err := err ++ "`pbv_decide` found a potentially spurious counterexample.\n"
    unless opaqueWidths.isEmpty do
      err := err ++ "  The following widths were abstracted as independent variables:\n"
      err := opaqueWidths.foldl (init := err) (fun acc e => acc ++ m!"    - {e}\n")
    unless opaqueVariables.isEmpty do
      err := err ++ "  The following expressions were abstracted as opaque variables:\n"
      err := opaqueVariables.foldl (init := err) (fun acc e => acc ++ m!"    - " ++ e ++ "\n")
    err := err ++ "Consider the following assignment:\n"

  -- Sort the counterexamples by name
  let widthCexsA := (widthCexs.filter fun tm _ => !(tm matches .widthLit _)).valuesArray |>
                      Array.qsort (lt := (fun a b => Name.lt a.name b.name))
  let bitvecCexs := bitvecCexs.qsort (fun a b => Name.lt a.name b.name)

  err := widthCexsA.foldl (init := err) (fun acc cex => acc ++ m!"  {cex}\n")
  err := bitvecCexs.foldl (init := err) (fun acc cex => acc ++ m!"  {cex}\n")

  return err

/--
Run `bv_decide` on a goal, throws with a pretty printed message if a
counterexample was found.
-/
public meta def closeWithBvDecide (goal : MVarId) (widthInfos : WidthInfos) (bvInfos : BitVecInfos) : TacticM Unit :=
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile {}
    let params ← Grind.mkDefaultParams {}

    match ← Grind.GrindM.run (params := params)
            <| bvDecide' (.mvarIdTarget goal) ctx with
    | .ok _ => return
    | .error counterExample => counterExample.goal.withContext do
        let error ← prettyPrintCounterExample counterExample widthInfos bvInfos
        throwError (← addMessageContextFull error)

end Veir.Meta.Tactic.PBVDecide
