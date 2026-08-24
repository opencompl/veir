module

public meta import Lean
public meta import Std
public import Veir.Data.PBV

open Lean Elab Tactic Meta Simp Std
namespace Veir.Data.PBV

/--
Information about the width variable and associated hypotheses.
-/
structure WidthInfo where
  /-- The Name correspodning to this width. -/
  widthName : Name
  /-- The Expr corresponding to this width. -/
  widthExpr : Expr
  /-- The FVarId corresponding to the new mask variable for this width. -/
  widthMaskFvar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The hypothesis that the width variable is less than the bmc bound. -/
  hypWidthLeBoundMVarId : MVarId
  /-- The FVar of the bound hypothesis, necessary so 'simp' rewrites with it. -/
  hypWidthLeBoundNote : FVarId


structure WidthInfos where
    /-- One WidthInfo per width -/
    infos : HashMap Expr WidthInfo := {}

meta def WidthInfos.push (this : WidthInfos) (info : WidthInfo) : WidthInfos :=
  { infos := this.infos.insert info.widthExpr info }

/--
Read-only configuration for the tactic.
-/
meta structure PbvTranslateContext where
  /-- The bound upto which we want to bitblast our widths. -/
   bmcBound : Nat

meta def introMaskWidth (ctx : PbvTranslateContext) (g : MVarId) (widthExpr : Expr) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
    -- Retrieve the ldecl from the context.
    let ldecl ← getFVarLocalDecl widthExpr
    -- Check that the Expr is of type Nat.
    assert! ldecl.type == (mkConst ``Nat)
    let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim #[mkNatLit ctx.bmcBound, widthExpr, ← g.getType]
      | throwError "width_elim should generate a goal"
    -- Intros
    let maskName := Name.mkSimple s!"m{ldecl.userName}"
    let (mask, g) ← g.withContext do g.intro maskName
    let (maskHyp, g) ← g.withContext do g.intro (Name.mkSimple s!"h_{maskName}")
    -- Define bounding conditions.
    let hypWidthLeBound ← g.withContext do
      -- Add a meaninful name using : (userName := Name.mkSimple "foo")
      mkFreshExprMVar (kind := .syntheticOpaque) (mkAppN (Expr.const ``LE.le [.zero])
        #[mkConst ``Nat, mkConst ``instLENat, widthExpr, mkNatLit ctx.bmcBound])
    g.withContext <| check hypWidthLeBound
    let (hypWidthLeBoundNote, g) ← g.withContext do g.note (Name.mkSimple s!"h_{ldecl.userName}_le_bound") hypWidthLeBound
    g.withContext <| check (mkFVar hypWidthLeBoundNote)
    -- Assert the BitVec mask constraint.
    let hypExpr ← g.withContext do mkAppM ``isMask_of_eq_maskOfWidth #[mkFVar maskHyp]
    let (_hIsMaskOfEq, g) ← g.withContext do g.note (Name.mkSimple s!"h_{maskName}_isMask") hypExpr

    let info : WidthInfo := {
      widthName := ldecl.userName,
      widthExpr := widthExpr,
      widthMaskFvar := mask,
      widthMaskHypFvar := maskHyp
      hypWidthLeBoundMVarId := hypWidthLeBound.mvarId!,
      hypWidthLeBoundNote
    }
    return (g, info, infos.push info)
    -- return (g, infos)

/--
Either get existing width info, or create one if it does not exist.
-/
meta def WidthInfos.getOrCreateInfo (ctx : PbvTranslateContext)
    (g : MVarId) (this : WidthInfos) (wExpr : Expr) : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
  if let some info := this.infos[wExpr]? then
    return (g, info, this)
  else
    introMaskWidth ctx g wExpr this


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
Match on an expression, and if it is a `BitVec w`, return the `w`.
Otherwise, return `none`.
-/
meta def getBitvecType? (e : Expr) : Option Expr :=
  match_expr e with
  | BitVec w => some w
  | _ => none

/--
Analyze a single local decl, and try to introduce it as a `BitVec` variable in our larger universe
if it is in fact a `BitVec` variable.
-/
meta def introBitvecFVarUnchecked (ctx : PbvTranslateContext) (g : MVarId)
      (bvInfos : BitVecInfos) (bvFVarId : FVarId) (widthInfo : WidthInfo) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  -- Find the BitVec {width_expr} variables.
    -- Revert to expose forall with the BitVec.
  let (#[oldVar], g) ← g.revert #[bvFVarId] | throwError "reverting shuold produce a var"
  -- Apply ``var_elim
  let (List.cons g _) ← g.withContext <| g.apply <| ← mkAppM ``var_elim
      #[mkNatLit ctx.bmcBound, widthInfo.widthExpr, .mvar widthInfo.hypWidthLeBoundMVarId]
    | throwError m!"{``var_elim} should generate a single goal. Produced {g}"
  -- Intros
  let name ← oldVar.getUserName
  let (bvVar, g) ← g.withContext <| g.intro name
  let widthMaskName ← widthInfo.widthMaskFvar.getUserName
  let (bvHyp, g) ← g.withContext <| g.intro <| Name.mkSimple s!"h_{name}_{widthMaskName}"
  return (g, bvInfos.push { bvVar, bvHyp })

/--
This creates a plan of bitvector fvars to be reverted, and their corresponding widths.
-/
structure BitVecFVarsToRevert where
  bvs : HashMap FVarId WidthInfo := {}

meta def BitVecFVarsToRevert.push (this : BitVecFVarsToRevert) (fvar : FVarId) (widthInfo : WidthInfo) : BitVecFVarsToRevert :=
  if this.bvs.contains fvar then  this
  else { bvs := this.bvs.insert fvar widthInfo }

/--
Given an expression, if it is of `BitVec w` type then create a mask for the
width `w`. If it is also an FVar, then it means it's a variable hence it has to
be added to the set of FVars to be reverted.
-/
meta def visitExprNonrec (ctx : PbvTranslateContext) (g : MVarId)
    (widthInfos : WidthInfos) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (MVarId × WidthInfos × BitVecFVarsToRevert) := g.withContext do
  let te ← g.withContext do inferType e
  if let some wExpr := getBitvecType? te then
    let (g, widthInfo, widthInfos) ← widthInfos.getOrCreateInfo ctx g wExpr
    if let some fvarId := e.fvarId? then
      return (g, widthInfos, bvs.push fvarId widthInfo)
    else
      return (g, widthInfos, bvs)
  else
    return (g, widthInfos, bvs)

/--
Visit an expression, collecting all widths and introducing mask variables.
For bitvectors, collect the bitvectors that need to be eliminated,
and then eliminate them all in the next step.
-/
meta partial def visitExprRec (ctx : PbvTranslateContext) (g : MVarId)
    (widthInfos : WidthInfos) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (MVarId × WidthInfos × BitVecFVarsToRevert) := g.withContext do
  let (g, widthInfos, bvs) ← visitExprNonrec ctx g widthInfos bvs e
  if e.isApp then
    let (f, args) := (e.getAppFn, e.getAppArgs)
    let (g, widthInfos, bvs) ← g.withContext do
      args.foldlM (init := (g, widthInfos, bvs)) fun (g, widthInfos, bvs) arg => g.withContext do visitExprRec ctx g widthInfos bvs arg
    visitExprRec ctx g widthInfos bvs f
  else
    return (g, widthInfos, bvs)

/--
Translate width precondition into BitVec hypothesis.
TODO: consider more complicated width exprs.
-/
meta def translateWidthPrecond (winfos : WidthInfos) (g : MVarId) (ldecl : LocalDecl) :
    MetaM (MVarId) := g.withContext do
  match_expr ldecl.type with
  | LT.lt ty _inst ea eb =>
    if ty == mkConst ``Nat then
      if let some wa := winfos.infos[ea]? then
        if let some wb := winfos.infos[eb]? then
          -- Apply mask_lt_mask using the known facts of the widths
          let bvLTExpr := mkAppM ``mask_lt_mask
            #[.fvar wa.hypWidthLeBoundNote,
              .fvar wb.hypWidthLeBoundNote,
              .fvar wa.widthMaskHypFvar,
              .fvar wb.widthMaskHypFvar,
              .fvar ldecl.fvarId]
          let (_mask_hyp, g) ← g.withContext do g.note (Name.mkSimple s!"bv_{wa.widthName}_lt_{wb.widthName}") (← bvLTExpr)
          logInfo m!"Translated {ldecl.toExpr} : {ldecl.type} to bitvec"
          return g
    return g
  | _ => return g

/--
Traverse the local context and translate any hypotheses on `Nat` widths into
`BitVec` hypotheses.
-/
meta def translateWidthPreconds (winfos: WidthInfos)
    (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  for ldecl in ← getLCtx do
    g ← translateWidthPrecond winfos g ldecl
  return g

/--
Eliminate the bitvector variables to introduce the masked versions.
-/
meta def introMaskedBitvectors (ctx : PbvTranslateContext)
    (bvs : BitVecFVarsToRevert) (g : MVarId) : MetaM (MVarId × BitVecInfos) := do
  bvs.bvs.foldM (init := (g, {})) fun (g, bvInfos) bvFvarId widthInfo =>
    introBitvecFVarUnchecked ctx g bvInfos bvFvarId widthInfo

/--
These rewrites introduce the toplevel equality that convers `a = b` into
`a.setWidth o &&& mask = b.setWidth o &&& mask`, which kickstarts the pushing process.
-/
meta def addToplevelRewrites (g : MVarId) (ctx : PbvTranslateContext) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  simp ← simp.addTheorem (.other ``eq_iff) <| (← mkAppM ``eq_iff #[mkNatLit ctx.bmcBound])
  return simp

/--
Add theorems to the Simp theorem context that push the `setWidth`s in.
TODO: make this a simp-set, called `pbv_push`, and just gather these
from the simp-set. This makes them user-extensible with no metaprogramming needed.
-/
meta def addPushTheorems (g : MVarId) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let others := #[``BitVec.setWidth_eq, ``setWidth_add, ``setWidth_setWidth]
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
Add theorems bounding each of width to the provided bound to the simp set.
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

meta def pbvTranslate (g : MVarId) (ctx : PbvTranslateContext) : MetaM (List MVarId) := g.withContext do
  -- throwError s!"Deciding with bound {ctx.bmcBound}"
  -- let (g, widthInfos) ← introMaskWidths ctx g
  -- Introduce bitvector variables
  let (g, widthInfos, bvsToRevert) ← visitExprRec ctx g {} {} (← g.getType)
  for (w, _winfo) in widthInfos.infos do
    g.withContext do logInfo m!"width: '{w}'"

  let (g, bvInfos) ← introMaskedBitvectors ctx bvsToRevert g
  let g ← translateWidthPreconds widthInfos g

  -- Run simp
  let thms := ← addToplevelRewrites g ctx
           <| ← addPushTheorems g
           <| ← addBvInfos g bvInfos -- This step is not strictly necessary.
           <| ← addWidthInfosSimpLemmas g widthInfos #[]

  let g ← applySimp g thms

  return [g] ++ (widthInfos.infos.values.map (·.hypWidthLeBoundMVarId))



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

example (w : Nat) (x y: BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide
  · grind

theorem trace_double_zero_extend (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).zeroExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind

theorem trace_triple_zero_extend (p q r t : Nat) (x : BitVec p)
  (hr : t <= 8)
  (hqr : q < r)
  (hpq : p < q)
  (hrt : r < t):
  ((x.zeroExtend q).zeroExtend r).zeroExtend t = x.zeroExtend t
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind
  · grind

theorem trace_zero_sign_extend (p q r : Nat) (x : BitVec p)
  (hr : r ≤ 8)
  (hqr : q < r)
  (hpq : p < q) :
  (x.zeroExtend q).signExtend r = x.zeroExtend r
  := by
  pbv_decide 8
  · bv_decide
  · grind
  · grind
  · grind
