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

def WidthInfo.widthFvarId (info : WidthInfo) : FVarId :=
  info.widthNatLocalDecl.fvarId

def WidthInfo.widthFvar (info : WidthInfo) : Expr :=
  .fvar info.widthFvarId

/--
Read-only configuration for the tactic.
-/
structure PbvTranslateContext where
  /-- the bound upto which we want to bitblast our widths. -/
   bmcBound : Nat

/-- Find the local declaration of the (single) width variable,
and eliminate it, producing the mask variable, and the masking contstraint.
-/
def introMaskWidths (ctx : PbvTranslateContext) (g : MVarId) : MetaM (MVarId × WidthInfo) := do
  g.withContext do
    for ldecl in ← getLCtx do
      unless ldecl.isImplementationDetail do
        if ← isDefEq ldecl.type (mkConst ``Nat) then
          let [g] ← g.withContext do
            g.apply <| ← mkAppM ``width_elim #[mkNatLit ctx.bmcBound, ldecl.toExpr, ← g.getType]
            | throwError "width_elim should generate a goal"
          let maskName := Name.mkSimple s!"m{ldecl.userName}"
          let (mask, g) ← g.withContext do g.intro maskName
          let (maskHyp, g) ← g.withContext do g.intro (Name.mkSimple s!"h_{maskName}")
          let hypWidthLeBound <- g.withContext do
            mkFreshExprMVar (mkAppN (Expr.const `Nat.le [])
              #[Expr.fvar ldecl.fvarId, mkNatLit ctx.bmcBound])
          g.withContext <| check hypWidthLeBound
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


structure BitVecInfo where
  bvVar : FVarId
  bvHyp : FVarId

structure BitVecInfos where
  infos : Array BitVecInfo := #[]

def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }

/--
Analyze a single local decl, and try to introduce it as a bitvec variable in our larger universe
if it is in fact a bitvec variable.
-/
def introVar (ctx : PbvTranslateContext) (widthInfo : WidthInfo) (g : MVarId)
      (infos : BitVecInfos) (ldecl : LocalDecl) :
      MetaM (MVarId × BitVecInfos) := g.withContext do
  unless ldecl.isImplementationDetail do
    -- Find the BitVec {width_expr} variables
    -- | TODO: replace defeq with syntactic eq, there are helpers in Lean/Meta or Lean/Tactic
    -- inside the bv_decide implementation.
    if ← isDefEq ldecl.type (mkApp (mkConst ``BitVec) widthInfo.widthFvar) then
      -- Revert to expose forall with the BitVec
      let (#[oldVar], g) ← g.revert #[ldecl.fvarId] | throwError "reverting shuold produce a var"
      let (List.cons g _) ← g.withContext <|  g.apply <| ← mkAppM ``var_elim
          #[mkNatLit ctx.bmcBound, widthInfo.widthFvar, .mvar widthInfo.hypWidthLeBound]
        | throwError m!"{``var_elim} should generate a single goal. Produced {g}"
      let name ← oldVar.getUserName
      let (bvVar, g) ← g.intro name
      let (bvHyp, g) ← g.intro <| Name.mkSimple s!"h_m{name}"
      return (g, infos.push { bvVar, bvHyp})
  return (g, infos)

/--
Apply the introVar to all localDecls to obtain concrete width bitvectors from parametric ones and the corresponding
hypotheses.
-/
def introVars (ctx : PbvTranslateContext) (g : MVarId) (widthInfo : WidthInfo) : MetaM (MVarId × BitVecInfos) := do
  let decls : LocalContext ← g.withContext getLCtx
  decls.foldlM (init := (g, {})) fun (g, infos) ldecl =>
    introVar ctx widthInfo g infos ldecl

/--
Add the harcoded push theorems to the Simp theorem context, bind each application to the
concrete blast width (`o`) and parametric width (`w`).
-/
def addPushTheorems (g : MVarId)
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
def addOtherTheorems (g : MVarId) (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let others := #[``BitVec.setWidth_eq]
  let mut simp := simp
  for n in others do
    simp ← simp.addTheorem (.other n) (mkConst n [])
  return simp

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
Add width mask hypothesis
-/
def addWidthHyp (g : MVarId) (widthInfo : WidthInfo)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  -- TODO: make this cleaner by collecting them all into a single array.
  let simpThms : SimpTheorems := {}
  let simpThms ← do
    simpThms.add (.other widthInfo.widthMaskHypFvar.name)
      #[] (mkFVar widthInfo.widthMaskHypFvar) (inv := true)
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
  let (g, widthInfo) ← introMaskWidths ctx g
  -- Introduce bitvector variables
  let (g, bvInfos) ← introVars ctx g widthInfo
  -- Run simp
  let g ← applySimp g <| ← addPushTheorems g widthInfo
                      <| ← addOtherTheorems g
                      <| ← addBvInfos g bvInfos
                      <| ← addWidthHyp g widthInfo #[]

  return [g, widthInfo.hypWidthLeBound]

syntax (name := pbvDecide) "pbv_decide" optConfig (ppSpace colGt num)? : tactic

@[tactic pbvDecide]
def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax



theorem trace_add_comm (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 13
  · bv_decide
  · grind

theorem trace_add (w : Nat) (x y z : BitVec w) (hw : w ≤ 4) :
  x + y + z= y + x +z := by
  pbv_decide 13
  · bv_decide
  · grind
