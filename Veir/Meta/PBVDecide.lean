import Std
import Lean
import Veir.Data.PBV

open Lean Elab Tactic Meta Simp Std
namespace Veir.Data.PBV

/--
Information about the width variable and associated hypotheses.
-/
structure WidthInfo where
  widthExpr : Expr
  /-- The FVarId corresponding to the new mask variable for this width. -/
  widthMaskFvar : FVarId
  /-- The FVarId of the pure-BV hypothesis that this width is a mask variable. -/
  widthMaskHypFvar : FVarId
  /-- The hypothesis that the width variable is less than the bmc bound. -/
  hypWidthLeBoundMVarId : MVarId
  /-- Hack: intro the bound as an fvar so 'simp' rewrites with it? this is ludicrous if true. -/
  hypWidthLeBoundNote : FVarId


structure WidthInfos where
    /-- One WidthInfo per width -/
    infos : HashMap Expr WidthInfo := {}

def WidthInfos.push (this : WidthInfos) (info : WidthInfo) : WidthInfos :=
  { infos := this.infos.insert info.widthExpr info }

/--
Read-only configuration for the tactic.
-/
structure PbvTranslateContext where
  /-- the bound upto which we want to bitblast our widths. -/
   bmcBound : Nat

def introMaskWidth (ctx : PbvTranslateContext) (g : MVarId) (ldecl : Expr) (infos : WidthInfos)
  : MetaM (MVarId × WidthInfo × WidthInfos) := g.withContext do
    -- TODO: check that the value has Nat.
    let [g] ← g.withContext do
      g.apply <| ← mkAppM ``width_elim #[mkNatLit ctx.bmcBound, ldecl, ← g.getType]
      | throwError "width_elim should generate a goal"
    -- Intros
    let maskName := Name.mkSimple s!"maskWidth_new_var" -- TODO: find the name if it's an Fvar, and otherwise abstract it into a new name.
    let (mask, g) ← g.withContext do g.intro maskName
    let (maskHyp, g) ← g.withContext do g.intro (Name.mkSimple s!"h_{maskName}")
    -- Define bounding conditions.
    let hypWidthLeBound <- g.withContext do
      mkFreshExprMVar (userName := Name.mkSimple "foo") (kind := .syntheticOpaque) (mkAppN (Expr.const ``LE.le [.zero])
        #[mkConst ``Nat, mkConst ``instLENat, ldecl, mkNatLit ctx.bmcBound])
    g.withContext <| check hypWidthLeBound
    let (hypWidthLeBoundNote, g) ← g.withContext do g.note (Name.mkSimple s!"hack_hyp_width_le_bound_{maskName}") hypWidthLeBound
    g.withContext <| check (mkFVar hypWidthLeBoundNote)
    -- Assert the BitVec mask constraint.
    let hypExpr ← g.withContext do mkAppM ``isMask_of_eq_maskOfWidth #[mkFVar maskHyp]
    let (_hIsMaskOfEq, g) ← g.note (Name.mkSimple s!"h_isMask_of_eq_{maskName}") hypExpr
    let info : WidthInfo := {
      widthExpr := ldecl,
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
def WidthInfos.getOrCreateInfo (ctx : PbvTranslateContext)
    (g : MVarId) (this : WidthInfos) (wExpr : Expr) : MetaM (MVarId × WidthInfo × WidthInfos) := do
  if let some info := this.infos[wExpr]? then
    return (g, info, this)
  else
    introMaskWidth ctx g wExpr this


/--
Pair of local facts about the converted `BitVec` variables.
-/
structure BitVecInfo where
  /-- The FVarId corresponding to the new concrete-width variable. -/
  bvVar : FVarId
  /-- The FVarId of the hypothesis encoding the mask constraint on the variable. -/
  bvHyp : FVarId

/--
Store information for all translated `BitVec`s.
-/
structure BitVecInfos where
  /-- The Array containing facts about each variable. -/
  infos : Array BitVecInfo := #[]

def BitVecInfos.push (this : BitVecInfos) (val : BitVecInfo) : BitVecInfos :=
  { this with infos := this.infos.push val }



/--
Match on an expression, and if it is a `BitVec w`, return the `w`.
Otherwise, return `none`.
-/
def getBitvecType? (e : Expr) : Option Expr :=
  match_expr e with
  | BitVec w => some w
  | _ => none

/--
Analyze a single local decl, and try to introduce it as a `BitVec` variable in our larger universe
if it is in fact a `BitVec` variable.
-/
def introBitvecVar (ctx : PbvTranslateContext) (widthInfos : WidthInfos) (g : MVarId)
      (bvInfos : BitVecInfos) (ldecl : LocalDecl) :
      MetaM (MVarId × WidthInfos × BitVecInfos) := g.withContext do
  unless ldecl.isImplementationDetail do
    -- Find the BitVec {width_expr} variables.
    if let some wExpr := getBitvecType? ldecl.type then
      let (g, widthInfo, widthInfos) ← widthInfos.getOrCreateInfo ctx g wExpr
      -- Revert to expose forall with the BitVec.
      let (#[oldVar], g) ← g.revert #[ldecl.fvarId] | throwError "reverting shuold produce a var"
      -- Apply ``var_elim
      let (List.cons g _) ← g.withContext <| g.apply <| ← mkAppM ``var_elim
          #[mkNatLit ctx.bmcBound, widthInfo.widthExpr, .mvar widthInfo.hypWidthLeBoundMVarId]
        | throwError m!"{``var_elim} should generate a single goal. Produced {g}"
      -- Intros
      let name ← oldVar.getUserName
      let (bvVar, g) ← g.intro name
      let (bvHyp, g) ← g.intro <| Name.mkSimple s!"h_m{name}"
      return (g, widthInfos, bvInfos.push { bvVar, bvHyp })
  return (g, widthInfos, bvInfos)

/--
Apply the introVar to all localDecls to obtain concrete width bitvectors from parametric ones and the corresponding
hypotheses.
-/
def introBitvecVars (ctx : PbvTranslateContext) (g : MVarId) :
    MetaM (MVarId × WidthInfos × BitVecInfos) := do
  let decls : LocalContext ← g.withContext getLCtx
  decls.foldlM (init := (g, {}, {})) fun (g, widthInfos, bvInfos) ldecl =>
    introBitvecVar ctx widthInfos g bvInfos ldecl


/--
These rewrites introduce the toplevel equality that convers `a = b` into
`a.setWidth o &&& mask = b.setWidth o &&& mask`, which kickstarts the pushing process.
-/
def addToplevelRewrites (g : MVarId) (widthInfos : WidthInfos) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for (_widthExpr, widthInfo) in widthInfos.infos do
    simp ← simp.addTheorem (.other ``eq_iff) <| (← mkAppM ``eq_iff #[mkFVar widthInfo.hypWidthLeBoundNote])
  return simp

/--
Add theorems to the Simp theorem context that push the `setWidth`s in.
TODO: make this a simp-set, called `pbv_push`, and just gather these
from the simp-set. This makes them user-extensible with no metaprogramming needed.
-/
def addPushTheorems (g : MVarId) (simp : SimpTheoremsArray) :
    MetaM SimpTheoremsArray := g.withContext do
  let others := #[``BitVec.setWidth_eq, ``eq_iff, ``setWidth_add, ``setWidth_setWidth]
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
Add BitVecInfos theorems to the Simp theorem context that don't need special bindings
-/
def addWidthInfosSimpLemmas (g : MVarId) (widthInfos : WidthInfos)
  (simp : SimpTheoremsArray) : MetaM SimpTheoremsArray := g.withContext do
  let mut simp := simp
  for (_wexpr, widthInfo) in widthInfos.infos do
    simp ← simp.addTheorem (.other widthInfo.hypWidthLeBoundNote.name)
        (mkFVar widthInfo.hypWidthLeBoundNote)
  return simp

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
  -- let (g, widthInfos) ← introMaskWidths ctx g
  -- Introduce bitvector variables
  let (g, widthInfos, bvInfos) ← introBitvecVars ctx g
  -- Run simp
  let thms := ← addToplevelRewrites g widthInfos
                      <| ← addPushTheorems g
                      <| ← addBvInfos g bvInfos
                      <| ← addWidthInfosSimpLemmas g widthInfos #[]
  let g ← applySimp g thms

  return [g] ++ (widthInfos.infos.values.map (·.hypWidthLeBoundMVarId))



/--
`pbv_decide` takes a `Nat` bound as input argument and uses it to translate a
parametric bitvector formula, containing a single width parameter, into a
concrete width formula.

The tactic generates two goals:
1. The desired concrete width formula that can be decided using `bv_decide`
2. A side-goal to prove that the width parameter is bounded by the provided
bound, this should be solvable by grind.
-/
syntax (name := pbvDecide) "pbv_decide" optConfig (ppSpace colGt num)? : tactic

@[tactic pbvDecide]
def evalPbvDecide : Tactic := fun stx => do
  match stx with
  | `(tactic| pbv_decide $n:num) => do
      let ctx : PbvTranslateContext := { bmcBound := n.getNat }
      replaceMainGoal (← pbvTranslate (← getMainGoal) ctx)
  | _ => throwUnsupportedSyntax


/-- Manual trace of the future tactic, transforming an unbounded parametric width
    statement into a bounded one and solving it up to the bound (4 in this case) -/
theorem trace_add_comm_manual (w : Nat) (x y : BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
-- Step 1: Bound widths to the provided blast width (redundant in this case)
  have w_le_bw :  w ≤ 4 := by grind
-- Step 2-3: Introduce mask to replace `w` Nat var
  apply width_elim 4 w
  intro mw h_mw
-- Step 4: Eliminate the parametric bv var of width `w`
--         enforcing width constraint with mask
  revert x
  apply var_elim 4 w w_le_bw
  intro x h_xmw
  revert y
  apply var_elim 4 w w_le_bw
  intro y h_ymw
-- Step 5: Convert width hypothesis to mask hypothesis
  have mw_mask := isMask_of_eq_maskOfWidth h_mw
-- Step 6: Remove natural numbers from goal and hyps, by pushing setWidths down
  simp only [
      eq_iff w_le_bw,             -- Introduce `setWidth` to goal
      setWidth_add,       -- Push `setWidth` down add
      setWidth_setWidth,  -- Push `setWidth` down setWidth
      BitVec.setWidth_eq,         -- Remove redundant setWidths
      w_le_bw]                     -- Replace mask with nat with bv constraint
      at h_xmw h_ymw ⊢
-- Step 8: Bitblast!
  bv_decide

set_option trace.Meta.Tactic.simp.all true
set_option trace.Meta.Tactic.simp true
example (w : Nat) (x y: BitVec w) (hw : w ≤ 4) :
  x + y = y + x := by
  pbv_decide 4
  · bv_decide
  · grind
