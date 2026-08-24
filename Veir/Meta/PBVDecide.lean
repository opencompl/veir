module

public meta import Lean
public import Veir.Data.PBV

open Lean Elab Tactic Meta Simp
namespace Veir.Data.PBV

/--
Information about the width variable and associated hypotheses.
-/
meta structure WidthInfo where
  /-- The LocalDecl corresponding to this width variable. -/
  widthNatLocalDecl : LocalDecl
  /-- The FVarId corresponding to the new mask variable for this width. -/
  widthMaskFvar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The hypothesis that the width variable is less than the bmc bound. -/
  hypWidthLeBound : MVarId

meta def WidthInfo.widthFvarId (info : WidthInfo) : FVarId :=
  info.widthNatLocalDecl.fvarId

meta def WidthInfo.widthFvar (info : WidthInfo) : Expr :=
  .fvar info.widthFvarId

/--
Read-only configuration for the tactic.
-/
meta structure PbvTranslateContext where
  /-- The bound upto which we want to bitblast our widths. -/
   bmcBound : Nat

/-- Find the local declaration of the (single) width variable,
and eliminate it, producing the mask variable, and the masking constraint.
-/
meta def introMaskWidths (ctx : PbvTranslateContext) (g : MVarId) : MetaM (MVarId × WidthInfo) := do
  g.withContext do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        if ← isDefEq ldecl.type (mkConst ``Nat) then
          -- Apply ``width_elim
          let [g] ← g.withContext do
            g.apply <| ← mkAppM ``width_elim #[mkNatLit ctx.bmcBound, ldecl.toExpr, ← g.getType]
            | throwError "width_elim should generate a goal"
          -- Intros
          let maskName := Name.mkSimple s!"m{ldecl.userName}"
          let (mask, g) ← g.withContext do g.intro maskName
          let (maskHyp, g) ← g.withContext do g.intro (Name.mkSimple s!"h_{maskName}")
          -- Define bounding conditions.
          let hypWidthLeBound <- g.withContext do
            mkFreshExprMVar (mkAppN (Expr.const `Nat.le [])
              #[Expr.fvar ldecl.fvarId, mkNatLit ctx.bmcBound])
          g.withContext <| check hypWidthLeBound
          -- Assert the BitVec mask constraint.
          let hypExpr ← g.withContext do mkAppM ``isMask_of_eq_maskOfWidth #[mkFVar maskHyp]
          let (_hIsMaskOfEq, g) ← g.note (Name.mkSimple s!"h_isMask_of_eq_{maskName}") hypExpr
          let info : WidthInfo := {
            widthNatLocalDecl := ldecl,
            widthMaskFvar := mask,
            widthMaskHypFvar := maskHyp
            hypWidthLeBound := hypWidthLeBound.mvarId!
          }
          return (g, info)
    throwError "unable to find a valid width variable."

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
Analyze a single local decl, and try to introduce it as a `BitVec` variable in our larger universe
if it is in fact a `BitVec` variable.
-/
meta def introVar (ctx : PbvTranslateContext) (widthInfo : WidthInfo) (g : MVarId)
      (infos : BitVecInfos) (ldecl : LocalDecl) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  unless ldecl.isImplementationDetail do
    -- Find the BitVec {width_expr} variables.
    if Expr.equal ldecl.type (mkApp (mkConst ``BitVec) widthInfo.widthFvar) then
      -- Revert to expose forall with the BitVec.
      let (#[oldVar], g) ← g.revert #[ldecl.fvarId] | throwError "reverting shuold produce a var"
      -- Apply ``var_elim
      let (List.cons g _) ← g.withContext <| g.apply <| ← mkAppM ``var_elim
          #[mkNatLit ctx.bmcBound, widthInfo.widthFvar, .mvar widthInfo.hypWidthLeBound]
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
meta def introVars (ctx : PbvTranslateContext) (g : MVarId) (widthInfo : WidthInfo) : MetaM (MVarId × BitVecInfos) := do
  let decls : LocalContext ← g.withContext getLCtx
  decls.foldlM (init := (g, {})) fun (g, infos) ldecl =>
    introVar ctx widthInfo g infos ldecl

/--
Add the hardcoded push theorems to the Simp theorem context, bind each application to the
concrete blast width (`o`) and parametric width (`w`).
-/
meta def addPushTheorems (g : MVarId)
    (widthInfo : WidthInfo) (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let thms := #[``eq_iff, ``setWidth_add, ``setWidth_setWidth] -- hardcoded theorems
  let mut simp := simp
  for thm in thms do
    let push_thm ← g.withContext do mkAppM thm #[.mvar widthInfo.hypWidthLeBound]
    simp ← simp.addTheorem (.other thm) push_thm
  return simp

/--
Add theorems to the Simp theorem context that don't need special bindings
-/
meta def addOtherTheorems (g : MVarId) (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let others := #[``BitVec.setWidth_eq]
  let mut simp := simp
  for n in others do
    simp ← simp.addTheorem (.other n) (mkConst n [])
  return simp

/--
Add BitVecInfos theorems to the Simp theorem context that don't need special bindings.
-/
meta def addBvInfos (g : MVarId) (bvInfos : BitVecInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for info in bvInfos.infos do
      simp ← simp.addTheorem (.other info.bvHyp.name) (mkFVar info.bvHyp)
  return simp

/--
Add width mask hypothesis
-/
meta def addWidthHyp (g : MVarId) (widthInfo : WidthInfo)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  -- TODO: make this cleaner by collecting them all into a single array.
  let simpThms : SimpTheorems := {}
  let simpThms ← do
    simpThms.add (.other widthInfo.widthMaskHypFvar.name)
      #[] (mkFVar widthInfo.widthMaskHypFvar) (inv := true)
  return simp.push simpThms

/--
Run simp on an MVarId given a set of simp theorems.
-/
meta def applySimp (g : MVarId) (simp : SimpTheoremsArray) : MetaM MVarId := g.withContext do
  let simpCtx ← Simp.mkContext (simpTheorems := simp)
  let (some g, _) ← g.withContext do simpTarget g simpCtx
    | throwError "goal solved by simp"
  return g

meta def pbvTranslate (g : MVarId) (ctx : PbvTranslateContext) : MetaM (List MVarId) := do
  -- throwError s!"Deciding with bound {ctx.bmcBound}"
  let (g, widthInfo) ← introMaskWidths ctx g
  -- Introduce bitvector variables
  let (g, bvInfos) ← introVars ctx g widthInfo
  -- Run simp
  let g ← applySimp g <| ← addPushTheorems g widthInfo
                      <| ← addOtherTheorems g
                      <| ← addBvInfos g bvInfos
                      <| ← addWidthHyp g widthInfo #[]

  return [g, widthInfo.hypWidthLeBound]

/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a
parametric bitvector formula, containing a single-width parameter, into a
concrete width formula.

The tactic generates two goals:
1. The desired concrete width formula that can be decided using `bv_decide`
2. A side-goal to prove that the width parameter is bounded by the provided
bound, this should be solvable by grind.
-/
syntax (name := pbvDecide) "pbv_decide" (ppSpace colGt num) : tactic

@[tactic pbvDecide]
public meta def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax
