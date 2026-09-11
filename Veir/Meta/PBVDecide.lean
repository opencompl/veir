module

public meta import Lean
public meta import Std
public import Veir.Data.PBV

open Lean Elab Tactic Meta Simp Std

/-- Check if an `Expr` is a `Nat`. -/
meta def Expr.isNat (e : Expr) : Bool := e.isConstOf ``Nat

/--
Match on an expression, and if it is a `BitVec w`, return the `w`.
Otherwise, return `none`.
-/
meta def getBitvecType? (e : Expr) : Option Expr :=
  match_expr e with
  | BitVec w => some w
  | _ => none

/-- Given `a b : Nat`, return `a < b`. -/
meta def mkNatLT (a b : Expr) : Expr :=
  mkApp2 (mkApp2 (mkConst ``LT.lt [0]) Nat.mkType Nat.mkInstLT) a b

namespace Veir.Data.PBV

/--
Read-only configuration for the tactic.
-/
meta structure PbvTranslateContext where
  /-- The bound up to which we want to bitblast our widths. -/
  bmcBound : Nat

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
| widthLt (v w : Tm .width) : Tm .prop
| widthLe (v w : Tm .width) : Tm .prop
| widthEq (v w : Tm .width) : Tm .prop
| and (v w : Tm .prop) : Tm .prop

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
together with the `Expr`s on either side. `>` and `≥` are normalized into
`widthLt` and `widthLe` by swapping the two sides. Returns `none` for anything
else, including the same relations at a type other than `Nat`.
-/
meta def matchWidthRel (e : Expr) :
    Option ((Tm TmKind.width → Tm TmKind.width → Tm TmKind.prop) × Expr × Expr) :=
  match_expr e with
  | LT.lt ty _inst ea eb => if Expr.isNat ty then some (.widthLt, ea, eb) else none
  | LE.le ty _inst ea eb => if Expr.isNat ty then some (.widthLe, ea, eb) else none
  | GT.gt ty _inst ea eb => if Expr.isNat ty then some (.widthLt, eb, ea) else none
  | GE.ge ty _inst ea eb => if Expr.isNat ty then some (.widthLe, eb, ea) else none
  | Eq ty ea eb          => if Expr.isNat ty then some (.widthEq, ea, eb) else none
  | _ => none

/--
Reify an `Expr` into a `Tm .prop`. Returns `none` if the expression is not a
supported prop, or if the subterms fail to reify as `Tm .width`s.
-/
meta partial def Tm.reifyProp (env : TmWidthEnv) (e : Expr) : MetaM (Option (Tm .prop)) := do
  if let some (rel, ea, eb) := matchWidthRel e then
    let some wa ← Tm.reifyWidth env ea | return none
    let some wb ← Tm.reifyWidth env eb | return none
    return some (rel wa wb)
  else
    match_expr e with
    | And ea eb => do
      let some pa ← Tm.reifyProp env ea | return none
      let some pb ← Tm.reifyProp env eb | return none
      return some (.and pa pb)
    | _ => return none

/--
Convert a `Tm` into an `Expr` given an environment.
-/
meta def Tm.toExpr {k : TmKind} (this : Tm k) (env : TmWidthEnv) : Expr :=
  match this with
  | .widthAtom id => env.width2expr[id]!
  | .widthAdd v w => mkNatAdd (v.toExpr env) (w.toExpr env)
  | .widthLt  v w => mkNatLT (v.toExpr env) (w.toExpr env)
  | .widthLe  v w => mkNatLE (v.toExpr env) (w.toExpr env)
  | .widthEq  v w => mkNatEq (v.toExpr env) (w.toExpr env)
  | .and      a b => mkAnd (a.toExpr env) (b.toExpr env)

/--
Generate a `Name` from a `Tm`. Uses the index of the atoms as the basic variable name.
-/
meta def Tm.toName {k : TmKind} (tm : Tm k) : Name :=
  match tm with
  | .widthAtom e  => Name.mkSimple s!"w{e}"
  | .widthAdd v w => Name.mkSimple s!"{v.toName}_add_{w.toName}"
  | .widthLt  v w => Name.mkSimple s!"{v.toName}_lt_{w.toName}"
  | .widthLe  v w => Name.mkSimple s!"{v.toName}_le_{w.toName}"
  | .widthEq  v w => Name.mkSimple s!"{v.toName}_eq_{w.toName}"
  | .and      a b => Name.mkSimple s!"{a.toName}_and_{b.toName}"

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
  /-- Width at which the bit-blasting occurs. -/
  blastWidth : Nat

meta def WidthInfos.push (this : WidthInfos) (info : WidthInfo) : WidthInfos :=
  { this with infos := this.infos.insert (info.widthTm.toName) info }

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
meta def introMaskWidth (g : MVarId) (widthTm : Tm .width) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
    -- Apply width_elim
    let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim
        #[mkNatLit infos.blastWidth, widthTm.toExpr infos.env, ← g.getType]
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
          mkNatLit infos.blastWidth])
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
Recurse through a `.width Tm`, converting `Nat` term into a `BitVec` mask, and
translating relations on the terms into relations on the `BitVec` (eg. add).
-/
meta def getOrCreateWidthMask (g : MVarId) (widthTm : Tm .width) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := do
  -- Check if this width term is already in widthInfos
  if let some info := infos.getFromTm? widthTm then
    return (g, info, infos)
  -- Otherwise, recurse through the term to create it
  match widthTm with
  | .widthAtom _ => introMaskWidth g widthTm infos
  | .widthAdd v w => do
    -- Get or create masks of the children
    let (g, vInfo, infos) ← getOrCreateWidthMask g v infos
    let (g, wInfo, infos) ← getOrCreateWidthMask g w infos
    -- Intro the mask for this term
    let (g, thisInfo, infos) ← introMaskWidth g widthTm infos
    -- Rewrite the mask of a sum of widths into a product of the masks (+ 1).
    let (_hyp, g) ← g.withContext do
      g.note (Name.mkSimple s!"bv_{widthTm.toName}") <| ← mkAppM ``add_eq_mul_of_maskOfWidth #[
        .fvar vInfo.hypWidthLeBoundNote,
        .fvar wInfo.hypWidthLeBoundNote,
        .fvar thisInfo.hypWidthLeBoundNote,
        .fvar vInfo.widthMaskHypFvar,
        .fvar wInfo.widthMaskHypFvar,
        .fvar thisInfo.widthMaskHypFvar
      ]

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
Given a `Tm .prop` and the `Expr` it was reified from, construct the expr that
corresponds to the `Prop` expressed in terms of the masks.
-/
meta def getMaskedExprFromProp (g : MVarId) (prop : Tm .prop) (proof : Expr)
    (widthInfos : WidthInfos) : MetaM (MVarId × WidthInfos × Expr) := g.withContext do
  -- Ensure the proof and prop match.
  unless ← isDefEq (← inferType proof) (prop.toExpr widthInfos.env)
    do throwError m!"Prop : {prop.toExpr widthInfos.env} doesn't match the proof : {← inferType proof}"
  -- Helper to apply a theorem for a binary operation on widths.
  let applyPropBinop (thm : Name) (v w : Tm .width) : MetaM (MVarId × WidthInfos × Expr) := do
    let (g, vInfo, widthInfos) ← getOrCreateWidthMask g v widthInfos
    let (g, wInfo, widthInfos) ← getOrCreateWidthMask g w widthInfos
    let expr ← g.withContext <| mkAppM thm #[
          .fvar vInfo.hypWidthLeBoundNote,
          .fvar wInfo.hypWidthLeBoundNote,
          .fvar vInfo.widthMaskHypFvar,
          .fvar wInfo.widthMaskHypFvar,
          proof,
        ]
    return (g, widthInfos, expr)
  -- Recurse over the prop structure
  match prop with
  | .widthLt v w => applyPropBinop ``lt_of_lt_of_eq_maskOfWidth v w
  | .widthLe v w => applyPropBinop ``le_of_le_of_eq_maskOfWidth v w
  | .widthEq v w => applyPropBinop ``eq_of_eq_of_eq_maskOfWidth v w
  | .and a b => do
    let (g, widthInfos, aExpr) ←
      getMaskedExprFromProp g a (← mkAppM ``And.left  #[proof]) widthInfos
    let (g, widthInfos, bExpr) ←
      getMaskedExprFromProp g b (← mkAppM ``And.right #[proof]) widthInfos
    let expr ← g.withContext <| mkAppM ``And.intro #[aExpr, bExpr]
    return (g, widthInfos, expr)

/--
If the given hypothesis can be reified as a width prop, convert it into a
statement about the width masks, creating new masks if needed.
-/
meta def translateWidthPrecond (g : MVarId) (ldecl : LocalDecl) (widthInfos : WidthInfos)
    : MetaM (MVarId × WidthInfos) := g.withContext do
  -- If the hypothesis cannot be reified, skip it.
  let some prop ← Tm.reifyProp widthInfos.env (ldecl.type) | return (g, widthInfos)
  -- Obtain the `Expr` of the prop in terms of the mask.
  let (g, widthInfos, expr) ← getMaskedExprFromProp g prop (ldecl.toExpr) widthInfos
  -- State the mask version of the prop
  let (_, g) ← g.note (Name.mkSimple s!"bv_{prop.toName}") expr
  return (g, widthInfos)

/--
Traverse the local context and add any width pre-conditions to the goal.
-/
meta def translateWidthPreconds (g : MVarId) (widthInfos : WidthInfos)
    : MetaM (MVarId × WidthInfos) := g.withContext do
  (← getLCtx).foldlM (init := (g, widthInfos)) fun (g, widthInfos) ldecl =>
    translateWidthPrecond g ldecl widthInfos

/--
Given the width terms in the formula, translate all `Nat` widths into `BitVec`
masks and introduce the hypotheses that model the masks.
-/
meta def introMaskWidths (g : MVarId) (widthTms : WidthTms) (blastWidth : Nat)
  : MetaM (MVarId × WidthInfos)
  := g.withContext do
  -- Intro all the masks
  widthTms.terms.foldM
    (init := (g, { env := widthTms.env, blastWidth }))
    fun (g, widthInfos) _ widthTm => do
      let (g, _, infos) ← getOrCreateWidthMask g widthTm.term widthInfos
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
      ``msb_eq_and_signBitOfMask_maskOfWidth_ne_zero,
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
  -- Introduce the width masks, bounded by the blast width
  let (g, widthInfos) ← introMaskWidths g widthTms blastWidth
  -- Find and translate conditions on the width vars
  let (g, widthInfos) ← translateWidthPreconds g widthInfos
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

Widths built out of width variables and `+` are supported. So are the width
relations `<`, `≤`, `>`, `≥` and `=`, and conjunctions (`∧`) of them, when they
occur as hypotheses: each is translated into the corresponding relation on the
width masks.

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
