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
  /-- The bound up to which we want to bitblast our widths. -/
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
An environment that maps the width atoms of a `Tm` to their `Expr`s.
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
  (← getLCtx).foldrM (init := {}) fun ldecl (widthEnv : TmWidthEnv) => do
      if let some width := getBitvecType? ldecl.type then
        let some _ := widthEnv.width2expr.idxOf? width | pure <| widthEnv.push width
        pure widthEnv
      else
        if Expr.isNat ldecl.type then
          pure <| widthEnv.push ldecl.toExpr
        else
          pure widthEnv

/--
Type to capture the expressions this tactic handles: `Nat` width terms and
the propositions relating them.
-/
inductive TmKind
| width
| prop

/--
Inductive data structure to express the terms that this tactic reasons about.
-/
inductive Tm : TmKind → Type
| widthAtom (id : Nat) : Tm .width
| widthAdd (v w : Tm .width) : Tm .width
| widthLT (v w : Tm .width) : Tm .prop
| widthLE (v w : Tm .width) : Tm .prop
| widthEQ (v w : Tm .width) : Tm .prop

/--
Function to reify an `Expr` into a `Tm`. This function constructs the tree holding
the width term. The environment holds the 'atom' `Expr`s which are the building
blocks of the terms.
-/
meta partial def Tm.reifyWidth (env : TmWidthEnv) (e : Expr) : MetaM (Option (Tm .width)) := do
  if let some id := env.width2expr.idxOf? e then
    -- An atom is an expression that is present in the Env.
    pure <| some (.widthAtom id)
  else
    match_expr e with
    | HAdd.hAdd ty _ _ _ ae be =>
        let .true := Expr.isNat ty | pure none
        let some a ← Tm.reifyWidth env ae | pure none
        let some b ← Tm.reifyWidth env be | pure none
        return some (widthAdd a b)
    | _ => pure none

/--
Match a width relation over `Nat`, returning the `Tm .prop` constructor for it
together with the `Expr`s on either side. `>` and `≥` are normalised into
`widthLT` and `widthLE` by swapping the two sides. Returns `none` for anything
else, including the same relations at a type other than `Nat`.
-/
meta def matchWidthRel (e : Expr) :
    Option ((Tm TmKind.width → Tm TmKind.width → Tm TmKind.prop) × Expr × Expr) :=
  match_expr e with
  | LT.lt ty _inst ea eb => if Expr.isNat ty then some (.widthLT, ea, eb) else none
  | LE.le ty _inst ea eb => if Expr.isNat ty then some (.widthLE, ea, eb) else none
  | GT.gt ty _inst ea eb => if Expr.isNat ty then some (.widthLT, eb, ea) else none
  | GE.ge ty _inst ea eb => if Expr.isNat ty then some (.widthLE, eb, ea) else none
  | Eq ty ea eb          => if Expr.isNat ty then some (.widthEQ, ea, eb) else none
  | _ => none

/--
Reify an `Expr` into a `Tm .prop`. Returns `none` if the expression is not a
width relation, or if either side of the relation fails to reify as a width.
-/
meta def Tm.reifyProp (env : TmWidthEnv) (e : Expr) : MetaM (Option (Tm .prop)) := do
  if let some (rel, ea, eb) := matchWidthRel e then
    let some wa ← Tm.reifyWidth env ea | return none
    let some wb ← Tm.reifyWidth env eb | return none
    return some (rel wa wb)
  else
    return none

/--
Convert a `Tm` into an `Expr` given an environment.
-/
meta def Tm.toExpr (this : Tm .width) (env : TmWidthEnv) : Expr :=
  match this with
  | .widthAtom id => env.width2expr[id]!
  | .widthAdd v w => mkNatAdd (v.toExpr env) (w.toExpr env)

/--
Generate a `Name` from a `Tm`. Uses the index of the atoms as the basic variable name.
-/
meta def Tm.toName (tm : Tm .width) : Name :=
  match tm with
  | .widthAtom e => Name.mkSimple s!"w{e}"
  | .widthAdd v w => Name.mkSimple s!"{v.toName}_add_{w.toName}"

/--
Compute an upper bound on the value of this width term: an atom is bounded by
the bmc bound, and a sum by the sum of the bounds of its parts.
The maximum over all widths gives the blast width used for the whole goal.
-/
meta def Tm.getUniverseWidthUpperBound (tm : Tm .width) (ctx : PbvTranslateContext) : Nat :=
  match tm with
  | .widthAtom _ => ctx.bmcBound
  | .widthAdd wa wb => wa.getUniverseWidthUpperBound ctx + wb.getUniverseWidthUpperBound ctx

/--
Structure to hold a width term.
-/
structure WidthTm where
  term : Tm .width

/--
Collect width terms into one data structure.
-/
structure WidthTms where
  /-- The width environment mapping `.atoms` to `Expr`. -/
  env : TmWidthEnv
  /-- The HashMap mapping a Name to a `WidthTm`. -/
  terms : HashMap Name WidthTm := {}

meta def WidthTms.push (this : WidthTms) (width : WidthTm) : WidthTms :=
{ terms := this.terms.insert (width.term.toName) width, env := this.env }

/--
Reify the width `Expr`, then either return the term already stored under that
name, or create and store a new one.
-/
meta def WidthTms.getOrCreateTm (g : MVarId) (this : WidthTms) (wExpr : Expr)
  : MetaM (MVarId × WidthTm × WidthTms) := g.withContext do
  let some reified ← Tm.reifyWidth this.env wExpr
    | throwError m!"Failed to reify width expr: {wExpr}"
  if let some info := this.terms[reified.toName]? then
    return (g, info, this)
  else
    let widthTm := { term := reified }
    return (g, widthTm, this.push widthTm)

/-- Get the maximum width needed for blasting across all widths. -/
meta def WidthTms.getUniverseWidthUpperBound (this : WidthTms)
    (ctx : PbvTranslateContext) : Nat :=
  this.terms.fold (fun val _e wTm =>
    val.max (wTm.term.getUniverseWidthUpperBound ctx)) ctx.bmcBound

/--
Information about the width variable and associated hypotheses.
-/
structure WidthInfo where
  /-- The Name corresponding to this width. -/
  widthName : Name
  /-- The `Tm` corresponding to this width. -/
  widthTm : Tm .width
  /-- The FVarId corresponding to the new mask variable for this width. -/
  widthMaskFvar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The proof obligation that the width variable is less than or equal to
      the blast bound. -/
  hypWidthLeBoundMVarId : MVarId
  /-- The hypothesis that the width variable is less than or equal to the blast
      bound. -/
  hypWidthLeBoundNote : FVarId

meta def WidthInfo.name (this : WidthInfo) : Name :=
  this.widthTm.toName

structure WidthInfos where
  /-- One WidthInfo per width -/
  infos : HashMap Name WidthInfo := {}
  /-- Width environment. -/
  env : TmWidthEnv

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
meta def WidthInfos.getFromExpr? (this : WidthInfos) (wExpr : Expr)
    : MetaM (Option WidthInfo) := do
  -- Reduce the expression (allows for cases such as (w + 0) to be reduced to w).
  let reducedExpr ← whnf wExpr
  -- Reify the expr using the env and then look for it in the Hashmap.
  let some reified ← Tm.reifyWidth this.env reducedExpr | pure none
  return this.infos[reified.toName]?

/--
Given a width term (`widthTm`), introduce a `BitVec` variable corresponding
to the mask of that width. Then introduce a hypothesis bounding the width to the
provided `blastWidth` and enforce it as a mask with `and_add_one_eq_zero_of_maskOfWidth`.
-/
meta def introMaskWidth (blastWidth : Nat) (g : MVarId) (widthTm : Tm .width) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
    -- Apply width_elim
    let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim #[mkNatLit blastWidth, widthTm.toExpr infos.env, ← g.getType]
      | throwError m!"{``width_elim} should generate a goal"
    -- Intros
    let name := widthTm.toName
    let maskName := Name.mkSimple s!"m_{name}"
    let (#[mask, maskHyp], g) ← g.withContext
      <| g.introN 2 [maskName, Name.mkSimple s!"h_{maskName}"]
      | throwError m!"Failed to intro {``width_elim}"
    -- Introduce width bound on the variable.
    let hypWidthLeBound ← g.withContext do
      mkFreshExprMVar (mkAppN (Expr.const ``LE.le [.zero])
        #[mkConst ``Nat,
          mkConst ``instLENat,
          widthTm.toExpr infos.env,
          mkNatLit blastWidth])
    g.withContext <| check hypWidthLeBound
    let (hypWidthLeBoundNote, g) ← g.withContext do g.note (Name.mkSimple s!"h_{name}_le_blast") hypWidthLeBound
    g.withContext <| check (mkFVar hypWidthLeBoundNote)
    -- Assert the BitVec mask constraint.
    let hypExpr ← g.withContext do mkAppM ``and_add_one_eq_zero_of_maskOfWidth #[mkFVar maskHyp]
    let (_, g) ← g.withContext do g.note (Name.mkSimple s!"h_{maskName}_bv_mask") hypExpr

    let info : WidthInfo := {
      widthName := name,
      widthTm := widthTm,
      widthMaskFvar := mask,
      widthMaskHypFvar := maskHyp
      hypWidthLeBoundMVarId := hypWidthLeBound.mvarId!,
      hypWidthLeBoundNote
    }
    return (g, info, infos.push info)

/--
Get the mask corresponding to a `Tm` from the `WidthInfos` if it exists, else
create it and return the updated `WidthInfos`.
-/
meta def WidthInfos.getOrCreateTm (this : WidthInfos) (g : MVarId)
  (term : Tm .width) (blastWidth : Nat)
  : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
  if let some info := this.getFromTm? term then
    return (g, info, this)
  else
    introMaskWidth blastWidth g term this

/--
Recurse through a `.width Tm`, converting `Nat` term into a `BitVec` mask, and
translating relations on the terms into relations on the `BitVec` (eg. add).
-/
meta def introMaskRec (blastWidth : Nat) (g : MVarId) (widthTm : Tm .width) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) :=
  match widthTm with
  | .widthAtom _ => infos.getOrCreateTm g widthTm blastWidth
  | .widthAdd v w => do
    let (g, vInfo, infos) ← introMaskRec blastWidth g v infos
    let (g, wInfo, infos) ← introMaskRec blastWidth g w infos
    if let some info := infos.getFromTm? widthTm then
      -- If the add term has already been declared, skip restating the hypothesis
        return (g, info, infos)
    else
      let (g, thisInfo, infos) ← introMaskWidth blastWidth g widthTm infos
      -- Rewrite the mask of a sum of widths into a product of the masks (+ 1).
      let (_hyp, g) ← g.withContext do
        g.note (Name.mkSimple s!"h_{widthTm.toName}_mask_mul")
        <| ← mkAppM ``add_eq_mul_of_maskOfWidth
        <| #[
          vInfo.hypWidthLeBoundNote,
          wInfo.hypWidthLeBoundNote,
          thisInfo.hypWidthLeBoundNote,
          vInfo.widthMaskHypFvar,
          wInfo.widthMaskHypFvar,
          thisInfo.widthMaskHypFvar
        ].map mkFVar

      return (g, thisInfo, infos)

/--
The `BitVec` variable that a parametric-width variable was converted into,
together with the hypothesis constraining it.
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
Analyze a single bitvector FVarId, and introduce it as a `BitVec` variable in
our larger universe. `Unchecked` because `widthTm` is trusted to be the width of
`bvFVarId`; it is not re-derived from the local context.
-/
meta def introBitvecFVarUnchecked (widthInfos : WidthInfos) (g : MVarId)
      (bvInfos : BitVecInfos) (bvFVarId : FVarId) (widthTm : WidthTm) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  -- Revert to expose forall with the BitVec.
  let (#[oldVar], g) ← g.revert #[bvFVarId]
    | throwError m!"Reverting {g} should produce a var."
  let wExpr := widthTm.term.toExpr widthInfos.env
  -- Apply ``var_elim.
  let some infos := widthInfos.getFromTm? widthTm.term
    | throwError m!"{wExpr} should have been defined in widthInfos."
  let [g] ← g.withContext <| g.apply <| ← mkAppM ``var_elim #[.fvar infos.hypWidthLeBoundNote]
    | throwError m!"{``var_elim} should generate a single goal. Produced {g}"

  let name ← oldVar.getUserName
  let (#[bvVar, bvHyp], g) ← g.withContext <| g.introN 2
    [name, Name.mkSimple s!"h_{name}_maskOfWidth_{widthTm.term.toName}"]
    | throwError m!"Expecting two intros from {g}"

  return (g, bvInfos.push { bvVar, bvHyp })

/--
A plan of the bitvector fvars to be reverted, and their corresponding widths.
-/
structure BitVecFVarsToRevert where
  bvs : HashMap FVarId WidthTm := {}

meta def BitVecFVarsToRevert.push (this : BitVecFVarsToRevert) (fvar : FVarId) (widthTm : WidthTm) : BitVecFVarsToRevert :=
  if this.bvs.contains fvar then this
  else { bvs := this.bvs.insert fvar widthTm }

/--
Given an expression, if it is of `BitVec w` type then create a term `Tm` for the
width `w`. If it is also an FVar then it is a variable, and hence has to be
added to the set of FVars to be reverted.
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
Visit an expression, collecting all widths and all bitvectors `FVars` that
correspond to individual bitvector variables.
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

/--
Extract `Tm .width`s and corresponding theorem from `Tm .prop`.
-/
meta def getThmFromProp (term : Tm .prop) : Name × Tm .width × Tm .width × String :=
  match term with
  | .widthLT v w => (``lt_of_lt_of_eq_maskOfWidth, v, w, "lt")
  | .widthLE v w => (``le_of_le_of_eq_maskOfWidth, v, w, "le")
  | .widthEQ v w => (``eq_of_eq_of_eq_maskOfWidth, v, w, "eq")

/--
If a statament in the local context that can be reified as a prop is found, then
convert into a statement about the width masks, instantiating new masks if needed.
-/
meta def translateWidthPrecond (blastWidth : Nat) (widthInfos : WidthInfos)
    (g : MVarId) (ldecl : LocalDecl)
    : MetaM (MVarId × WidthInfos) := g.withContext do
  -- If the hypothesis cannot be reified, skip it
  let some prop ← Tm.reifyProp widthInfos.env (ldecl.type) | return (g, widthInfos)
  -- Get the theorem matching the prop
  let (thm, v, w, str) := getThmFromProp prop
  -- Get or create the masks for the width terms
  let (g, vInfo, widthInfos) ← introMaskRec blastWidth g v widthInfos
  let (g, wInfo, widthInfos) ← introMaskRec blastWidth g w widthInfos
  -- Apply the theorem to convert the width condition into a `BitVec` condition.
  let (_, g) ← g.withContext
    <| g.note (Name.mkSimple s!"bv_{v.toName}_{str}_{w.toName}")
    <| ← g.withContext <| mkAppM thm <| #[
        vInfo.hypWidthLeBoundNote,
        wInfo.hypWidthLeBoundNote,
        vInfo.widthMaskHypFvar,
        wInfo.widthMaskHypFvar,
        ldecl.fvarId,
      ].map mkFVar

  return (g, widthInfos)

/--
Traverse the local context and add any width pre-conditions to the goal.
-/
meta def translateWidthPreconds (blastWidth : Nat) (winfos : WidthInfos)
    (g : MVarId) : MetaM (MVarId × WidthInfos) := g.withContext do
  (← getLCtx).foldlM (
    init := (g, winfos))
    fun (g, widthInfos) ldecl =>
      translateWidthPrecond blastWidth widthInfos g ldecl

/--
Given the width terms in the formula, translate all `Nat` widths into `BitVec`
masks and introduce the hypotheses that model the masks.
-/
meta def introMaskWidths (blastWidth : Nat) (widthTms : WidthTms) (g : MVarId)
  : MetaM (MVarId × WidthInfos)
  := g.withContext do
  -- Intro all the masks
  widthTms.terms.foldM
    (init := (g, { env := widthTms.env }))
    fun (g, widthInfos) _ widthTm => do
      let (g, _, infos) ← introMaskRec blastWidth g widthTm.term widthInfos
      return (g, infos)

/--
Eliminate the bitvector variables to introduce the masked versions.
-/
meta def introMaskedBitvectors (bvs : BitVecFVarsToRevert) (g : MVarId)
    (widthInfos : WidthInfos) : MetaM (MVarId × BitVecInfos) := do
  bvs.bvs.foldM (init := (g, {})) fun (g, bvInfos) bvFvarId widthTm => do
    introBitvecFVarUnchecked widthInfos g bvInfos bvFvarId widthTm

/--
Add the theorems that need the blast width pre-filled before they can be used
within the Simp set.
-/
meta def addBoundRewrites (g : MVarId) (blastWidth : Nat) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let thms := #[
        ``eq_iff,
        ``msb_eq_and_signBitOfMask_maskOfWidth_ne_zero
  ]

  thms.foldlM (init := simp) fun simps name =>
    return ← simps.addTheorem (.other name)
      <| ← mkAppM name #[mkNatLit blastWidth]

/--
Add theorems to the Simp theorem context that push the `setWidth`s in.
-/
meta def addPushTheorems (g : MVarId) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let others := #[
      ``BitVec.setWidth_eq,
      ``setWidth_add,
      ``setWidth_setWidth,
      ``setWidth_append_eq_or_mul_maskOfWidth_add_one,
      ``signBitOfMask_eq,
      ``setWidth_signExtend_eq_and_maskOfWidth,
  ]

  let mut simp := simp
  for n in others do
    simp ← simp.addTheorem (.other n) (mkConst n [])
  return simp

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
  return simp

/--
Run simp on an MVarId given a set of simp theorems.
Throws if `simp` closes the goal outright.
-/
meta def applySimp (g : MVarId) (simp : SimpTheoremsArray) : MetaM MVarId := g.withContext do
  let simpCtx ← Simp.mkContext (simpTheorems := simp)
  let (some g, _) ← g.withContext do simpTarget g simpCtx
    | throwError "goal solved by simp"
  return g

/-- Helper to run grind on a given `MVarId`. Returns a `some MVarId`
    if the goal couldn't be proven. -/
meta def runGrind (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let result ← Grind.main g <| ← Grind.mkDefaultParams {}
  return result.failure?.map (·.mvarId)

/-- Run `grind` on each `MVarId` in widthInfos. -/
meta def runGrindOnSubgoals (g : MVarId) (infos : WidthInfos) : MetaM (List MVarId) := g.withContext do
  let subgoals := List.reduceOption <| ← infos.infos.values.mapM (runGrind ·.hypWidthLeBoundMVarId)
  for remainingSubgoal in subgoals do
    logWarning m!"`grind` could not prove the following : {remainingSubgoal}"
  return subgoals

meta def pbvTranslate (g : MVarId) (ctx : PbvTranslateContext) : MetaM (List MVarId)
  := g.withContext do
  -- Construct the width environment
  let widthEnv ← createWidthEnv g
  -- Find `BitVec`s and intro their widths
  let (g, widthTms, bvsToRevert) ← visitExprRec g { env := widthEnv } {} (← g.getType)
  -- Compute the blast width
  let blastWidth := widthTms.getUniverseWidthUpperBound ctx
  -- Introduce the width masks, bounded by the max width
  let (g, widthInfos) ← introMaskWidths blastWidth widthTms g
  -- Find and translate conditions on the width vars
  let (g, widthInfos) ← translateWidthPreconds blastWidth widthInfos g
  -- Intro the `BitVec`s
  let (g, bvInfos) ← introMaskedBitvectors bvsToRevert g widthInfos
  -- Create simp set
  let thms := ← addBoundRewrites g blastWidth
           <| ← addPushTheorems g
           <| ← addBvInfos g bvInfos -- This step is not strictly necessary.
           <| ← addWidthInfosSimpLemmas g widthInfos #[]
  -- Run simp
  let g ← applySimp g thms
  -- Run grind on subgoals
  let subgoals ← runGrindOnSubgoals g widthInfos
  -- Return modified goal and subgoals.
  return g :: subgoals

/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a
parametric bitvector formula into a concrete width formula.

Widths built out of width variables and `+` are supported, as are the width
relations `<`, `≤`, `>`, `≥` and `=` occurring as hypotheses, which are
translated into the corresponding relations on the width masks.

The tactic generates multiple goals:
1. The desired concrete width formula that can be decided using `bv_decide`.
2. Multiple side-goals to prove that the width parameters are bounded by the
computed blast width. These should be solvable by `grind`.
-/
syntax (name := pbvDecide) "pbv_decide" (ppSpace colGt num) : tactic

@[tactic pbvDecide]
public meta def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax
