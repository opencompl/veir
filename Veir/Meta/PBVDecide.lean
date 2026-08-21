import Lean
import Veir.Data.PBV

open Lean Elab Tactic Meta Simp
namespace Veir.Data.PBV

structure WidthInfo where
  /-- The local decl corresponding to this width variable. -/
  widthNatLocalDecl : LocalDecl
  /-- The fvar corresponding to the new mask variable for this width. -/
  widthMaskFvar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The hypothesis that the width variable is less than the bmc bound. -/
  hypWidthLeBound : MVarId
  /-- `hypWidthLeBound`, introduced into the local context. Simp needs a real hypothesis, not an
  unassigned metavariable, to discharge the `v ≤ o` side conditions of the push theorems. -/
  hypWidthLeBoundFvar : FVarId

def WidthInfo.widthFvarId (info : WidthInfo) : FVarId :=
  info.widthNatLocalDecl.fvarId

def WidthInfo.widthFvar (info : WidthInfo) : Expr :=
  .fvar info.widthFvarId

/-- The user-facing name of the width variable, used to name the facts we derive from it. -/
def WidthInfo.widthUserName (info : WidthInfo) : Name :=
  info.widthNatLocalDecl.userName

/-- Find the `WidthInfo` for `e`, if `e` is one of the width variables we eliminated. -/
def findWidthInfo? (widthInfos : Array WidthInfo) (e : Expr) : Option WidthInfo :=
  widthInfos.find? fun info => Expr.equal e info.widthFvar

/--
Read-only configuration for the tactic.
-/
structure PbvTranslateContext where
  /-- the bound upto which we want to bitblast our widths. -/
   bmcBound : Nat

/-- Eliminate a single width variable, producing the mask variable, and the masking constraint. -/
def introMaskWidth (ctx : PbvTranslateContext) (g : MVarId) (ldecl : LocalDecl) :
    MetaM (MVarId × WidthInfo) := do
  -- Apply ``width_elim
  let [g] ← g.withContext do
    g.apply <| ← mkAppM ``width_elim #[mkNatLit ctx.bmcBound, ldecl.toExpr, ← g.getType]
    | throwError "width_elim should generate a goal"
  -- Intros
  let maskName := Name.mkSimple s!"m{ldecl.userName}"
  let (mask, g) ← g.withContext do g.intro maskName
  let (maskHyp, g) ← g.withContext do g.intro (Name.mkSimple s!"h_{maskName}")
  -- Define bounding conditions. Stated with `LE.le` rather than `Nat.le`, so that this bound
  -- matches the `v ≤ o` side conditions of the conditional push theorems syntactically.
  let boundType ← g.withContext do
    mkAppM ``LE.le #[Expr.fvar ldecl.fvarId, mkNatLit ctx.bmcBound]
  let hypWidthLeBound ← g.withContext do mkFreshExprMVar boundType
  g.withContext <| check hypWidthLeBound
  -- Introduce the bound into the local context, leaving its proof as an open side goal.
  let (hypWidthLeBoundFvar, g) ← g.note
    (Name.mkSimple s!"h_{ldecl.userName}_le_bound") hypWidthLeBound boundType
  -- Assert the BitVec mask constraint, unfolded, else `bv_decide` cannot use it.
  let hypExpr ← g.withContext do
    mkAppM ``and_add_one_eq_zero_of_eq_maskOfWidth #[mkFVar maskHyp]
  let (_hIsMaskOfEq, g) ← g.note (Name.mkSimple s!"h_isMask_of_eq_{maskName}") hypExpr
  return (g, {
    widthNatLocalDecl := ldecl,
    widthMaskFvar := mask,
    widthMaskHypFvar := maskHyp
    hypWidthLeBound := hypWidthLeBound.mvarId!
    hypWidthLeBoundFvar := hypWidthLeBoundFvar
  })

/-- Find the local declarations of every width variable, and eliminate each of them.
A statement may mention several widths at once (`x.zeroExtend q |>.signExtend r`, say),
so every `Nat` in the context is treated as a width.
-/
def introMaskWidths (ctx : PbvTranslateContext) (g : MVarId) :
    MetaM (MVarId × Array WidthInfo) := do
  let natDecls ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc ldecl => do
      if ldecl.isImplementationDetail then return acc
      if ← isDefEq ldecl.type (mkConst ``Nat) then return acc.push ldecl
      return acc
  if natDecls.isEmpty then
    throwError "unable to find a valid width variable."
  let mut g := g
  let mut infos : Array WidthInfo := #[]
  for ldecl in natDecls do
    let (g', info) ← introMaskWidth ctx g ldecl
    g := g'
    infos := infos.push info
  return (g, infos)


structure BitVecInfo where
  bvVar : FVarId
  bvHyp : FVarId

structure BitVecInfos where
  infos : Array BitVecInfo := #[]

def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }

/--
Analyze a single local decl, and try to introduce it as a bitvec variable in our larger universe
if it is in fact a `BitVec` variable of one of the parametric widths.
-/
def introVar (ctx : PbvTranslateContext) (widthInfos : Array WidthInfo) (g : MVarId)
      (infos : BitVecInfos) (ldecl : LocalDecl) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  unless ldecl.isImplementationDetail do
    -- Find the BitVec {width_expr} variables.
    for widthInfo in widthInfos do
      if Expr.equal ldecl.type (mkApp (mkConst ``BitVec) widthInfo.widthFvar) then
        -- Revert to expose forall with the BitVec.
        let (#[oldVar], g) ← g.revert #[ldecl.fvarId] | throwError "reverting shuold produce a var"
        -- Apply ``var_elim
        let (List.cons g _) ← g.withContext <| g.apply <| ← mkAppM ``var_elim
            #[mkNatLit ctx.bmcBound, widthInfo.widthFvar, mkFVar widthInfo.hypWidthLeBoundFvar]
          | throwError m!"{``var_elim} should generate a single goal. Produced {g}"
        -- Intros
        let name ← oldVar.getUserName
        let (bvVar, g) ← g.intro name
        let (bvHyp, g) ← g.intro <| Name.mkSimple s!"h_m{name}"
        return (g, infos.push { bvVar, bvHyp})
  return (g, infos)

/--
Apply the introVar to all localDecls to obtain concrete width bitvectors from parametric ones and the corresponding
hypotheses.
-/
def introVars (ctx : PbvTranslateContext) (g : MVarId) (widthInfos : Array WidthInfo) :
    MetaM (MVarId × BitVecInfos) := do
  let decls : LocalContext ← g.withContext getLCtx
  decls.foldlM (init := (g, {})) fun (g, infos) ldecl =>
    introVar ctx widthInfos g infos ldecl

/--
Translate the ordering conditions on the natural number widths (`p < q`) into facts about the
corresponding bitvector masks (`mp < mq`), which are the only form the bitblaster can see.
-/
def introMaskOrders (g : MVarId) (widthInfos : Array WidthInfo) : MetaM MVarId := do
  let cands ← g.withContext do
    (← getLCtx).foldlM (init := #[]) fun acc (ldecl : LocalDecl) => do
      if ldecl.isImplementationDetail then return acc
      let (``LT.lt, #[ty, _inst, lhs, rhs]) := ldecl.type.getAppFnArgs | return acc
      unless ty.isConstOf ``Nat do return acc
      let some infoLhs := findWidthInfo? widthInfos lhs | return acc
      let some infoRhs := findWidthInfo? widthInfos rhs | return acc
      return acc.push (ldecl, infoLhs, infoRhs)
  let mut g := g
  for (ldecl, infoLhs, infoRhs) in cands do
    let proof ← g.withContext do
      mkAppM ``mask_lt_mask
        #[mkFVar infoLhs.hypWidthLeBoundFvar, mkFVar infoRhs.hypWidthLeBoundFvar,
          mkFVar infoLhs.widthMaskHypFvar, mkFVar infoRhs.widthMaskHypFvar, ldecl.toExpr]
    let name := Name.mkSimple s!"h_m{infoLhs.widthUserName}_lt_m{infoRhs.widthUserName}"
    let (_hMaskLt, g') ← g.note name proof
    g := g'
  return g

/--
Add the hardcoded push theorems to the Simp theorem context, bind each application to the
concrete blast width (`o`) and parametric width (`w`). Each theorem is instantiated once per
width variable, since a single goal may mix several parametric widths.
-/
def addPushTheorems (g : MVarId)
    (widthInfos : Array WidthInfo) (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray :=
  g.withContext do
  -- hardcoded theorems taking the `w ≤ o` bound as their first explicit argument
  let thms := #[``eq_iff, ``setWidth_add, ``setWidth_setWidth, ``msb_eq_and_maskOfWidth_ne_zero]
  let mut simp := simp
  for info in widthInfos do
    for thm in thms do
      let push_thm ← g.withContext do mkAppM thm #[mkFVar info.hypWidthLeBoundFvar]
      simp ← simp.addTheorem (.other <| thm.appendAfter s!"_{info.widthUserName}") push_thm
    -- The bound itself, so that simp can discharge the `v ≤ o` side condition of the
    -- conditional push theorems such as `setWidth_signExtend_eq_and_maskOfWidth`.
    simp ← simp.addTheorem (.other info.hypWidthLeBoundFvar.name)
      (mkFVar info.hypWidthLeBoundFvar)
  return simp

/--
Add theorems to the Simp theorem context that don't need special bindings
-/
def addOtherTheorems (g : MVarId) (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray :=
  g.withContext do
  let others := #[``BitVec.setWidth_eq, ``BitVec.zeroExtend_eq_setWidth,
    ``setWidth_signExtend_eq_and_maskOfWidth]
  -- Unfolded, else `bv_decide` abstracts them away as opaque atoms.
  let unfolds := #[``signBitOfMask]
  let mut simp := simp
  for n in others do
    simp ← simp.addTheorem (.other n) (mkConst n [])
  let mut unfoldThms : SimpTheorems := {}
  for n in unfolds do
    unfoldThms ← unfoldThms.addDeclToUnfold n
  return simp.push unfoldThms

/--
Add BitVecInfos theorems to the Simp theorem context that don't need special bindings
-/
def addBvInfos (g : MVarId) (bvInfos : BitVecInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for info in bvInfos.infos do
      simp ← simp.addTheorem (.other info.bvHyp.name) (mkFVar info.bvHyp)
  return simp

/--
Add the width mask hypotheses, used in reverse to replace `maskOfWidth o w` by the mask variable.
-/
def addWidthHyps (g : MVarId) (widthInfos : Array WidthInfo)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simpThms : SimpTheorems := {}
  for info in widthInfos do
    simpThms ← simpThms.add (.other info.widthMaskHypFvar.name)
      #[] (mkFVar info.widthMaskHypFvar) (inv := true)
  return simp.push simpThms

/--
Run simp on an MVarId given a set of simp theorems
-/
def applySimp (g : MVarId) (simp : SimpTheoremsArray) : MetaM MVarId := g.withContext do
  let simpCtx ← Simp.mkContext (simpTheorems := simp)
  let (some g, _) ← g.withContext do simpTarget g simpCtx
    | throwError "goal solved by simp"
  return g

def pbvTranslate (g : MVarId) (ctx : PbvTranslateContext) : MetaM (List MVarId) := do
  -- throwError s!"Deciding with bound {ctx.bmcBound}"
  let (g, widthInfos) ← introMaskWidths ctx g
  -- Introduce bitvector variables
  let (g, bvInfos) ← introVars ctx g widthInfos
  -- Translate width orderings into mask orderings
  let g ← introMaskOrders g widthInfos
  -- Run simp
  let g ← applySimp g <| ← addPushTheorems g widthInfos
                      <| ← addOtherTheorems g
                      <| ← addBvInfos g bvInfos
                      <| ← addWidthHyps g widthInfos #[]

  return g :: (widthInfos.map (·.hypWidthLeBound)).toList

/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a
parametric bitvector formula into a concrete width formula. The tactic generates
one goal per width parameter, plus one for the translated formula: the first,
containing the desired concrete width formula that can be decided using
`bv_decide`; the rest containing side-goals to prove that each width parameter is
bounded by the provided bound, in the order the width parameters appear in the
local context.
-/
syntax (name := pbvDecide) "pbv_decide" optConfig (ppSpace colGt num)? : tactic

@[tactic pbvDecide]
def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax
