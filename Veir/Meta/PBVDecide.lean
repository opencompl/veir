module

public meta import Lean
public meta import Std
public import Veir.Data.PBV

open Lean Elab Tactic Meta Simp Std
namespace Veir.Data.PBV

/--
Read-only configuration for the tactic.
-/
meta structure PbvTranslateContext where
  /-- The bound upto which we want to bitblast our widths. -/
   bmcBound : Nat

meta def Expr.isNat (e : Expr) : Bool := e.isConstOf ``Nat

/--
Match on an expression, and if it is a `BitVec w`, return the `w`.
Otherwise, return `none`.
-/
meta def getBitvecType? (e : Expr) : Option Expr :=
  match_expr e with
  | BitVec w => some w
  | _ => none

/--
An environment that maps width atoms in `Tm` into its `Expr`
-/
meta structure TmWidthEnv where
  width2expr : Array Expr := #[]

meta def TmWidthEnv.push (this : TmWidthEnv) (width : Expr) : TmWidthEnv :=
  { width2expr := this.width2expr.push width }

/--
Traverse the local context to extract the width 'atoms' that make up width
expressions. These are either width `Expr`s coming from `BitVec w` or
`Nat` variables in the local context.
-/
meta def createWidthEnv (g : MVarId) : MetaM TmWidthEnv := g.withContext do
  (← getLCtx).foldrM (init := {}) fun ldecl (widthEnv : TmWidthEnv ) => do
      if let some width := getBitvecType? ldecl.type then
        let some _ := widthEnv.width2expr.idxOf? width | pure <| widthEnv.push width
        pure widthEnv
      else
        if Expr.isNat ldecl.type then
          pure <| widthEnv.push ldecl.toExpr
        else
          pure widthEnv

/--
Type to capture the expressions this tactic will handle.
Only capture `width` at the moment.
-/
inductive TmKind
| width

/--
Inductive data structure to express the terms that this tactic reasons about.
-/
inductive Tm : TmKind → Type
| widthAtom (id : Nat) : Tm .width

/--
Function to Reify an `Expr` into a `Tm`. This function constructs the tree holding
the width term. The environment holds the 'atom' `Expr`s which are the building
blocks of the terms.
-/
meta partial def Tm.reifyWidth (env : TmWidthEnv) (e : Expr) : MetaM (Option (Tm .width)) := do
  if let some id := env.width2expr.idxOf? e then
    -- An atom is an expression that is present in the Env.
    pure <| some (.widthAtom id)
  else
    pure none

/--
Convert a `Tm` into an `Expr` given an environment.
-/
meta def Tm.toExpr (this : Tm .width) (env : TmWidthEnv) : Expr :=
  match this with
  | .widthAtom id => env.width2expr[id]!

/--
Generate a `Name` from a `Tm`. Uses the index of the atoms as the basic variable name.
-/
meta def Tm.toName (tm: Tm .width) : Name :=
  match tm with
  | .widthAtom e => Name.mkSimple s!"w{e}"

structure WidthTm where
  term : Tm .width

structure WidthTms where
  env : TmWidthEnv
  terms: HashMap Name WidthTm := {}

meta def WidthTms.push (this : WidthTms) (width : WidthTm) : WidthTms :=
{ terms := this.terms.insert (width.term.toName) width, env := this.env }

/--
Either get existing width term, or try and reify one if it does not exist.
-/
meta def WidthTms.getOrCreateTm (g : MVarId) (this : WidthTms) (wExpr : Expr)
  : MetaM (MVarId × WidthTm × WidthTms) := g.withContext do
  let some reified ← Tm.reifyWidth this.env wExpr
    | throwError m!"Failed to reify width expr: {wExpr}"
  if let some info := this.terms[reified.toName]? then -- use reified.toExpr as a kind of "normal"/"canonical" form
    return (g, info, this)
  else
    let widthTm := { term := reified }
    return (g, widthTm, this.push widthTm)

/--
Information about the width variable and associated hypotheses.
-/
structure WidthInfo where
  /-- The Name corresponding to this width. -/
  widthName : Name
  /-- The Expr corresponding to this width. -/
  widthTm : Tm .width
  /-- The FVarId corresponding to the new mask variable for this width. -/
  widthMaskFvar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The hypothesis that the width variable is less than the bmc bound. -/
  hypWidthLeBoundMVarId : MVarId
  /-- The FVar of the bound hypothesis, necessary so 'simp' rewrites with it. -/
  hypWidthLeBoundNote : FVarId

meta def WidthInfo.name (this : WidthInfo) : Name :=
  this.widthTm.toName

structure WidthInfos where
  /-- One WidthInfo per width -/
  infos : HashMap Name WidthInfo := {}
  /-- Width Environemnt -/
  env: TmWidthEnv

meta def WidthInfos.push (this : WidthInfos) (info : WidthInfo) : WidthInfos :=
  { infos := this.infos.insert (info.widthTm.toName) info, env := this.env }

/--
Get WidthInfo from a Term.
-/
meta def WidthInfos.getFromTm? (this : WidthInfos) (wTm : Tm .width) : Option WidthInfo :=
  this.infos[wTm.toName]?

/--
Get WidthInfo from an Expr.
-/
meta def WidthInfos.getFromExpr? (this: WidthInfos) (wExpr : Expr)
    : MetaM (Option WidthInfo) := do
  -- Reduce the expression (allows for cases such as (w + 0) to be reduced to w).
  let reducedExpr ← whnf wExpr
  -- Reify the expr using the env and then look for it in the Hashmap.
  let some reified ← Tm.reifyWidth this.env reducedExpr | pure none
  return this.infos[reified.toName]?

meta def introMaskWidth (maxBound : Nat) (g : MVarId) (widthTm : WidthTm) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfos) := g.withContext do
    -- Apply width_elim
    let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim #[mkNatLit maxBound, widthTm.term.toExpr infos.env, ← g.getType]
      | throwError m!"{``width_elim} should generate a goal"
    -- Intros
    let name := widthTm.term.toName
    let maskName := Name.mkSimple s!"m_{name}"
    let (#[mask, maskHyp], g) ← g.withContext
      <| g.introN 2 [maskName, Name.mkSimple s!"h_{maskName}"]
      | throwError m!"Failed to intro {``width_elim}"
    -- Introduce width bound on the variable.
    let hypWidthLeBound ← g.withContext do
      mkFreshExprMVar (mkAppN (Expr.const ``LE.le [.zero])
        #[mkConst ``Nat,
          mkConst ``instLENat,
          widthTm.term.toExpr infos.env,
          mkNatLit maxBound])
    g.withContext <| check hypWidthLeBound
    let (hypWidthLeBoundNote, g) ← g.withContext do g.note (Name.mkSimple s!"h_{name}_le_blast") hypWidthLeBound
    g.withContext <| check (mkFVar hypWidthLeBoundNote)
    -- Assert the BitVec mask constraint.
    let hypExpr ← g.withContext do mkAppM ``maskOfWidth_and_add_one_eq_zero #[mkFVar maskHyp]
    let (_, g) ← g.withContext do g.note (Name.mkSimple s!"h_{maskName}_bv_mask") hypExpr

    let info : WidthInfo := {
      widthName := name,
      widthTm := widthTm.term,
      widthMaskFvar := mask,
      widthMaskHypFvar := maskHyp
      hypWidthLeBoundMVarId := hypWidthLeBound.mvarId!,
      hypWidthLeBoundNote
    }
    return (g, infos.push info)

/--
Pair of local facts about the converted `BitVec` variables.
-/
meta structure BitVecInfo where
  /-- The FVarId corresponding to the new concrete-width variable. -/
  bvVar : FVarId
  /-- The FVarId of the hypothesis encoding the mask constraint on the variable. -/
  bvHyp : FVarId

/--
Store information for all translated `BitVec`s.
-/
meta structure BitVecInfos where
  /-- The Array containing facts about each variable. -/
  infos : Array BitVecInfo := #[]

meta def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }

/--
Analyze a single bitvector FVarId, and try to introduce it as a `BitVec`
variable in our larger universe.
-/
meta def introBitvecFVarUnchecked (widthInfos : WidthInfos) (g : MVarId)
      (bvInfos : BitVecInfos) (bvFVarId : FVarId) (widthTm : WidthTm) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  -- Revert to expose forall with the BitVec.
  let (#[oldVar], g) ← g.revert #[bvFVarId]
    | throwError m!"Reverting {g} shuold produce a var."
  let wExpr := widthTm.term.toExpr widthInfos.env
  -- Apply ``var_elim.
  let some infos := widthInfos.getFromTm? widthTm.term
    | throwError m!"{wExpr} Shuold have be defined in widthInfos."
  let [g] ← g.withContext <| g.apply <| ← mkAppM ``var_elim #[.fvar infos.hypWidthLeBoundNote]
    | throwError m!"{``var_elim} should generate a single goal. Produced {g}"

  let name ← oldVar.getUserName
  let (#[bvVar, bvHyp], g) ← g.withContext <| g.introN 2
    [name, Name.mkSimple s!"h_{name}_maskOfWidth_{widthTm.term.toName}"]
    | throwError m!"Expecting two intros from {g}"

  return (g, bvInfos.push { bvVar, bvHyp })

/--
This creates a plan of bitvector fvars to be reverted, and their corresponding widths.
-/
structure BitVecFVarsToRevert where
  bvs : HashMap FVarId WidthTm := {}

meta def BitVecFVarsToRevert.push (this : BitVecFVarsToRevert) (fvar : FVarId) (widthTm : WidthTm) : BitVecFVarsToRevert :=
  if this.bvs.contains fvar then  this
  else { bvs := this.bvs.insert fvar widthTm }

/--
Given an expression, if it is of `BitVec w` type then create a mask for the
width `w`. If it is also an FVar, then it means it's a variable hence it has to
be added to the set of FVars to be reverted.
-/
meta def visitExprNonrec (g : MVarId)
    (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (MVarId × WidthTms × BitVecFVarsToRevert) := g.withContext do
  let te ← g.withContext do inferType e
  if let some wExpr := getBitvecType? te then
    let (g, widthTm, widthTms) ← widthTms.getOrCreateTm g wExpr
    if let some fvarId := e.fvarId? then
      return (g, widthTms, bvs.push fvarId widthTm)
    else
      return (g, widthTms, bvs)
  else
    return (g, widthTms, bvs)

/--
Visit an expression, collecting all widths and introducing mask variables.
For bitvectors, collect the bitvectors that need to be eliminated,
and then eliminate them all in the next step.
-/
meta partial def visitExprRec (g : MVarId)
    (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (MVarId × WidthTms × BitVecFVarsToRevert) := g.withContext do
  let (g, widthTms, bvs) ← visitExprNonrec g widthTms bvs e
  if e.isApp then
    let (f, args) := (e.getAppFn, e.getAppArgs)
    let (g, widthTms, bvs) ← g.withContext do
      args.foldlM (init := (g, widthTms, bvs)) fun (g, widthTms, bvs) arg =>
      g.withContext do visitExprRec g widthTms bvs arg
    visitExprRec g widthTms bvs f
  else
    return (g, widthTms, bvs)

meta def introMaskWidths (widthTms : WidthTms) (g : MVarId) (ctx : PbvTranslateContext)
  : MetaM (MVarId × WidthInfos)
  := g.withContext do
  -- Intro all the masks
  widthTms.terms.foldM (init := (g, { env := widthTms.env })) (fun (g, widthInfos) _ widthTm =>
    introMaskWidth ctx.bmcBound g widthTm widthInfos
  )

/--
Eliminate the bitvector variables to introduce the masked versions.
-/
meta def introMaskedBitvectors (bvs : BitVecFVarsToRevert) (g : MVarId)
    (widthInfos : WidthInfos) : MetaM (MVarId × BitVecInfos) := do
  bvs.bvs.foldM (init := (g, {})) fun (g, bvInfos) bvFvarId widthTm => do
    introBitvecFVarUnchecked widthInfos g bvInfos bvFvarId widthTm
/--
These theorems require pre-filling the width bound in order to be used within
the Simp set.
-/
meta def addBoundRewrites (g : MVarId) (ctx : PbvTranslateContext)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let thms := #[``eq_iff]

  thms.foldlM (init := simp) fun simps name =>
    return ← simps.addTheorem (.other name)
      <| ← mkAppM name #[mkNatLit <| ctx.bmcBound]

/--
Add theorems to the Simp theorem context that push the `setWidth`s in.
-/
meta def addPushTheorems (g : MVarId) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let others := #[
      ``BitVec.setWidth_eq,
      ``setWidth_add,
      ``setWidth_setWidth,
  ]

  let mut simp := simp
  for n in others do
    simp ← simp.addTheorem (.other n) (mkConst n [])
  return simp

/--
Add BitVecInfos theorems to the Simp theorem context. Simplify the final formula
to remove redundant masking operations, not strictly necessary for `bv_decide`
to decide the resulting formula.
-/
meta def addBvInfos (g : MVarId) (bvInfos : BitVecInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for info in bvInfos.infos do
      simp ← simp.addTheorem (.other info.bvHyp.name) (mkFVar info.bvHyp)
  return simp

/--
Add theorems bounding each width to the provided bound to the simp set.
-/
meta def addWidthInfosSimpLemmas (g : MVarId) (widthInfos : WidthInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for (_wexpr, widthInfo) in widthInfos.infos do
    simp ← simp.addTheorem (.other widthInfo.hypWidthLeBoundNote.name)
        (mkFVar widthInfo.hypWidthLeBoundNote)
  return simp

/--
Run simp on an MVarId given a set of simp theorems.
-/
meta def applySimp (g : MVarId) (simp : SimpTheoremsArray) : MetaM MVarId := g.withContext do
  let simpCtx ← Simp.mkContext (simpTheorems := simp)
  let (some g, _) ← g.withContext do simpTarget g simpCtx
    | throwError "goal solved by simp"
  return g

meta def pbvTranslate (g : MVarId) (ctx : PbvTranslateContext) : MetaM (List MVarId)
  := g.withContext do
  -- Construct the width environment
  let widthEnv ← createWidthEnv g
  -- Find `BitVec`s and intro their widths
  let (g, widthTms, bvsToRevert) ← visitExprRec g { env := widthEnv } {} (← g.getType)
  -- Introduce the width masks, bounded by the max width
  let (g, widthInfos) ← introMaskWidths widthTms g ctx
  -- Intro the `BitVec`s
  let (g, bvInfos) ← introMaskedBitvectors bvsToRevert g widthInfos
  -- Create simp set
  let thms := ← addBoundRewrites g ctx
           <| ← addPushTheorems g
           <| ← addBvInfos g bvInfos -- This step is not strictly necessary.
           <| ← addWidthInfosSimpLemmas g widthInfos #[]
  -- Run simp
  let g ← applySimp g thms
  -- Return modified goal and subgoals.
  return g :: (widthInfos.infos.values.map (·.hypWidthLeBoundMVarId))

/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a
parametric bitvector formula, containing a single-width parameter, into a
concrete width formula.

The tactic generates multiple goals:
1. The desired concrete width formula that can be decided using `bv_decide`
2. Multiple side-goals to prove that the width parameters are bounded by the
provided bound, these should be solvable by grind.
-/
syntax (name := pbvDecide) "pbv_decide" (ppSpace colGt num) : tactic

@[tactic pbvDecide]
public meta def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax
