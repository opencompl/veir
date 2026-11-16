module

public meta import Lean
public meta import Std
public import Lean.Meta.Tactic.BVDecide.Main
public meta import Veir.Meta.Tactic.PBVDecide.Basic
public meta import Veir.Meta.Tactic.PBVDecide.Reify

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
  /-- The original parametric-width variable, in the goal before the translation. -/
  origVar : FVarId

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
meta def getWidthCounterExamples (translated : Translated) (counterExample : CounterExample) : MetaM WidthMaskCexs := do
  let mut widthMaskCexs : WidthMaskCexs := {}

  for (widthTm, winfo) in translated.widthInfos do
    let name ← widthTm.toName
    let originalNatWidth := widthTm.toExpr translated.env
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
  bvInfos.mapM (fun bvinfo => counterExample.goal.withContext do
    let name ← bvinfo.bvVar.getUserName
    match findFVarIdInCounterExample? counterExample bvinfo.bvVar with
    | some (eq, bv) => do
      let some widthCex := widthCexs[bvinfo.bvWidthTm]?
        | throwError m!"Width ({← bvinfo.bvWidthTm.toName}) of BitVec {name} is missing from the generated counterexamples."
      return {counterExample := (eq, bv), width := widthCex, name, origVar := bvinfo.origVar}
    | none =>
      throwError m!"No counterexample generated for BitVec {name}"
  )

/--
If `e` is a leaf `t.setWidth o` of a `BitVec` of a translated width, the leaf `t`
together with the value of the atom truncated to the width of `t`.
-/
meta def leafCounterExample? (translated : Translated) (widthCexs : WidthMaskCexs)
    (e : Expr) (bv : BVExpr.PackedBitVec) : MetaM (Option MessageData) := do
  let_expr BitVec.setWidth w _ t := e | return none
  let (widthTm, _) ← ReifyM.run (Tm.reifyWidth w) { env := translated.env }
  let some widthCex := widthCexs[widthTm]? | return none
  return some m!"{t} = {bv.bv.setWidth widthCex.val}"

/-- The outcome of checking a decoded counterexample against the original goal. -/
meta inductive CexCheck where
  /-- The assignment satisfies every hypothesis and falsifies the goal. -/
  | confirmed
  /-- The assignment does not falsify the original goal. -/
  | spurious (reason : MessageData)
  /-- The assignment could not be evaluated on the original goal. -/
  | unchecked (reason : MessageData)

/--
Decide a closed proposition by evaluating its `Decidable` instance. Returns
`none` if `p` is not closed, has no instance, or does not reduce to a literal.
-/
meta def evalDecide? (p : Expr) : MetaM (Option Bool) := do
  if p.hasFVar || p.hasMVar then return none
  try
    let r ← withAtLeastTransparency .default <| whnf (← mkDecide p)
    if r.isConstOf ``true then return some true
    if r.isConstOf ``false then return some false
    return none
  catch _ => return none

/--
Check a decoded counterexample against the original, untranslated goal
`origGoal`. Width variables are replaced by their decoded values and `BitVec`
variables by literals, and each hypothesis and the goal are then decided by
evaluation. A hypothesis that holds is replaced by its `decide` proof, so that
later hypotheses and the goal that mention it become closed.

The counterexample is confirmed only if every hypothesis holds and the goal is
false; any other free variable (e.g. one that is neither a width nor a
`BitVec`) leaves it unchecked.
-/
meta def checkCounterExample (origGoal : MVarId) (widthCexs : WidthMaskCexs)
    (bitvecCexs : BitVecCexs) (counterExample : CounterExample) : MetaM CexCheck :=
  origGoal.withContext do
  let mut fvars : Array Expr := #[]
  let mut vals : Array Expr := #[]
  -- Width variables take their decoded values
  for (widthTm, cex) in widthCexs do
    if let .widthFVar _ fid := widthTm then
      fvars := fvars.push (.fvar fid)
      vals := vals.push (mkNatLit cex.val)
  let widthFVars := fvars
  let widthVals := vals
  -- `BitVec` variables become literals at their (instantiated) width
  for cex in bitvecCexs do
    let some w := getBitvecType? (← instantiateMVars (← cex.origVar.getType)) | continue
    let w := w.replaceFVars widthFVars widthVals
    fvars := fvars.push (.fvar cex.origVar)
    vals := vals.push <| mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit cex.assignedVal.toNat)
  -- Concrete-width `BitVec` variables of the original goal take their value directly
  for (e, bv) in counterExample.equations do
    let some fid := e.fvarId? | continue
    unless (← getLCtx).contains fid && !fvars.contains e do continue
    let some w := getBitvecType? (← instantiateMVars (← fid.getType)) | continue
    let some n := w.nat? | continue
    unless n == bv.w do continue
    fvars := fvars.push e
    vals := vals.push <| mkApp2 (mkConst ``BitVec.ofNat) w (mkNatLit bv.bv.toNat)
  -- Every hypothesis must hold
  let mut undecided : Option MessageData := none
  for ldecl in ← getLCtx do
    if ldecl.isImplementationDetail || ldecl.isLet then continue
    unless ← isProp ldecl.type do continue
    let ty := (← zetaReduce (← instantiateMVars ldecl.type)).replaceFVars fvars vals
    match ← evalDecide? ty with
    | some true =>
      fvars := fvars.push ldecl.toExpr
      vals := vals.push (← mkDecideProof ty)
    | some false =>
      return .spurious m!"it violates the hypothesis {ldecl.userName} : {ty}"
    | none =>
      if undecided.isNone then
        undecided := some m!"the hypothesis {ldecl.userName} : {ty} could not be decided"
  -- The goal must be false
  let target := (← zetaReduce (← instantiateMVars (← origGoal.getType))).replaceFVars fvars vals
  match ← evalDecide? target with
  | some false => return match undecided with
    | some reason => .unchecked reason
    | none => .confirmed
  | some true => return .spurious m!"the goal holds for it: {target}"
  | none => return .unchecked (undecided.getD m!"the goal {target} could not be decided")

/--
Convert a `bv_decide` counterexample into a message, mapping concrete mask `BitVec`
values to concrete width `Nat` values, and keeping track if any counterexamples
belong to expressions which have been abstracted as opaque variables, or if any
widths were abstracted as atoms independent of the other widths.
-/
meta def prettyPrintCounterExample (counterExample : CounterExample) (translated : Translated)
    (origGoal : MVarId) : MetaM MessageData := do
  let widthCexs ← getWidthCounterExamples translated counterExample
  let bitvecCexs ← getBitVecCounterExamples translated.bitvecInfos widthCexs counterExample

  let visitedExamples : HashSet Expr := widthCexs.fold (fun acc _ cex => acc.insert cex.counterExample.fst)
                                     <| bitvecCexs.foldl (fun acc cex => acc.insert cex.counterExample.fst) {}

  let opaqueVariables : Array MessageData ← counterExample.equations.filterMapM
    (fun (eq, bv) => counterExample.goal.withContext do
      if visitedExamples.contains eq then
        return none
      -- Leaves are shown as values of their own width
      if let some leaf ← leafCounterExample? translated widthCexs eq bv then
        return m!"{leaf} ({eq} = {bv.bv})"
      return m!"{eq} = {bv.bv}"
    )

  -- Widths that are neither variables, literals nor sums are atoms whose masks
  -- are unrelated to the masks of the other widths.
  let opaqueWidths : Array Expr :=
    translated.widthInfos.keys.filterMap (fun | .widthAtom id => some id | _ => none)
      |>.toArray.qsort (· < ·) |>.map (translated.env[·]!)

  let check ← checkCounterExample origGoal widthCexs bitvecCexs counterExample

  let mut err := m!""
  match check with
  | .confirmed =>
    err := err ++ "`pbv_decide` found a counterexample, consider the following assignment:\n"
  | .spurious reason | .unchecked reason =>
    err := err ++ "`pbv_decide` found a potentially spurious counterexample.\n"
    unless opaqueWidths.isEmpty do
      err := err ++ "  The following widths were abstracted as independent variables:\n"
      err := opaqueWidths.foldl (init := err) (fun acc e => acc ++ m!"    - {e}\n")
    unless opaqueVariables.isEmpty do
      err := err ++ "  The following expressions were abstracted as opaque variables:\n"
      err := opaqueVariables.foldl (init := err) (fun acc e => acc ++ m!"    - " ++ e ++ "\n")
    if check matches .spurious _ then
      err := err ++ m!"  The assignment does not falsify the original goal: {reason}.\n"
    else
      err := err ++ m!"  The assignment could not be checked against the original goal: {reason}.\n"
    err := err ++ "Consider the following assignment:\n"

  -- Sort the counterexamples by name
  let widthCexsA := (widthCexs.filter fun tm _ => !(tm matches .widthLit _)).valuesArray |>
                      Array.qsort (lt := (fun a b => Name.lt a.name b.name))
  let bitvecCexs := bitvecCexs.qsort (fun a b => Name.lt a.name b.name)

  err := widthCexsA.foldl (init := err) (fun acc cex => acc ++ m!"  {cex}\n")
  err := bitvecCexs.foldl (init := err) (fun acc cex => acc ++ m!"  {cex}\n")
  if check matches .confirmed then
    err := err ++ "The assignment satisfies the hypotheses and falsifies the original goal."

  return err

/--
Run `bv_decide` on a goal, throws with a pretty printed message if a
counterexample was found.
-/
public meta def closeWithBvDecide (goal : MVarId) (translated : Translated) (origGoal : MVarId) :
    TacticM Unit :=
  IO.FS.withTempFile fun _ lratFile => do
    let ctx ← TacticContext.new lratFile {}
    let params ← Grind.mkDefaultParams {}

    match ← Grind.GrindM.run (params := params)
            <| bvDecide' (.mvarIdTarget goal) ctx with
    | .ok _ => return
    | .error counterExample => counterExample.goal.withContext do
        let error ← prettyPrintCounterExample counterExample translated origGoal
        throwError (← addMessageContextFull error)

end Veir.Meta.Tactic.PBVDecide
