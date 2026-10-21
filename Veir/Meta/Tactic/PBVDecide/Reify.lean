module

public meta import Veir.Meta.Tactic.PBVDecide.Config

public section

open Lean Meta Std

namespace Veir.Meta.Tactic.PBVDecide

meta def Expr.isNat (e : Expr) : Bool := e.isConstOf ``Nat

meta def getBitvecType? (e : Expr) : Option Expr :=
  match_expr e with
  | BitVec w => some w
  | _ => none

meta def mkNatLT (a b : Expr) : Expr :=
  mkApp2 (mkApp2 (mkConst ``LT.lt [0]) Nat.mkType Nat.mkInstLT) a b

/--
An environment that maps the width atoms of a `Tm` to their `Expr`s.
-/
meta structure TmWidthEnv where
  width2expr : Array Expr := #[]

meta def TmWidthEnv.push (this : TmWidthEnv) (width : Expr) : TmWidthEnv :=
  { width2expr := this.width2expr.push width }

/--
Traverse the local context to extract the width 'atoms' that make up width
expressions. These are either width `Expr`s coming from `BitVec w` (unless w is
a numeric literal) or `Nat` variables in the local context.
-/
meta def createWidthEnv (g : MVarId) : MetaM TmWidthEnv := g.withContext do
  (← getLCtx).foldrM (init := {}) fun ldecl widthEnv => do
    if let some width := getBitvecType? ldecl.type then
      if width.nat?.isSome || widthEnv.width2expr.contains width then
        return widthEnv
      return widthEnv.push width
    if Expr.isNat ldecl.type then
      return widthEnv.push ldecl.toExpr
    return widthEnv

/--
Type to capture the expressions this tactic handles: `Nat` width terms and
the propositions relating them.
-/
inductive TmKind
| width
| prop

meta inductive Tm : TmKind → Type
| widthLit (val : Nat) : Tm .width
| widthAtom (id : Nat) : Tm .width
| widthAdd (v w : Tm .width) : Tm .width
| widthLt (v w : Tm .width) : Tm .prop
| widthLe (v w : Tm .width) : Tm .prop
| widthEq (v w : Tm .width) : Tm .prop
| and (v w : Tm .prop) : Tm .prop
deriving BEq, Hashable

abbrev WidthTm := Tm .width
abbrev WidthProp := Tm .prop

meta partial def Tm.reifyWidth (env : TmWidthEnv) (e : Expr) : MetaM (Option WidthTm) := do
  if let some id := env.width2expr.idxOf? e then
    -- An atom is an expression that is present in the Env.
    return some (.widthAtom id)
  else if let some val := e.nat? then
    return some (widthLit val)
  else
    match_expr e with
    | HAdd.hAdd ty _ _ _ ae be =>
        let .true := Expr.isNat ty | pure none
        let some a ← Tm.reifyWidth env ae | pure none
        let some b ← Tm.reifyWidth env be | pure none
        return some (widthAdd a b)
    | _ => return none

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

meta def Tm.toExpr {k : TmKind} (this : Tm k) (env : TmWidthEnv) : Expr :=
  match this with
  | .widthLit val => mkNatLit val
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
  | .widthLit val => Name.mkSimple s!"lit{val}"
  | .widthAtom e  => Name.mkSimple s!"w{e}"
  | .widthAdd v w => Name.mkSimple s!"{v.toName}_add_{w.toName}"
  | .widthLt  v w => Name.mkSimple s!"{v.toName}_lt_{w.toName}"
  | .widthLe  v w => Name.mkSimple s!"{v.toName}_le_{w.toName}"
  | .widthEq  v w => Name.mkSimple s!"{v.toName}_eq_{w.toName}"
  | .and      a b => Name.mkSimple s!"{a.toName}_and_{b.toName}"

/--
Compute an upper bound on the widths in this term: an atom is bounded by the
bmc bound, a sum by the sum of the bounds of its parts, and a prop by the
maximum of the bounds of its parts.
The maximum over all widths and width props gives the blast width used for the
whole goal.
-/
meta def Tm.getWidthUpperBound {k : TmKind} (tm : Tm k) (ctx : PbvDecideContext) : Nat :=
  match tm with
  | .widthLit val => val
  | .widthAtom _ => ctx.bmcBound
  | .widthAdd wa wb => wa.getWidthUpperBound ctx + wb.getWidthUpperBound ctx
  | .widthLt  v w
  | .widthLe  v w
  | .widthEq  v w
  | .and      v w => (v.getWidthUpperBound ctx).max (w.getWidthUpperBound ctx)

structure WidthTms where
  env : TmWidthEnv
  /-- The set of width terms found in the goal. -/
  terms : HashSet WidthTm := {}

meta def WidthTms.push (this : WidthTms) (width : WidthTm) : WidthTms :=
{ this with terms := this.terms.insert width }

/-- Get the maximum width needed for blasting across all widths. -/
meta def WidthTms.getWidthUpperBound (this : WidthTms)
    (ctx : PbvDecideContext) : Nat :=
  this.terms.fold (fun val wTm =>
    val.max (wTm.getWidthUpperBound ctx)) ctx.bmcBound

structure WidthProps where
  env : TmWidthEnv
  /-- A map from a `Tm .prop` to the `Nat` proof it was reified from -/
  props : HashMap WidthProp Expr := {}

/-- Insert a `WidthProp`, checking that the type of `expr` matches the `Tm`. -/
meta def WidthProps.pushProp (this : WidthProps) (prop : Tm .prop) (expr : Expr) : MetaM WidthProps := do
  unless ← isDefEq (← inferType expr) (prop.toExpr this.env)
    do throwError m!"Cannot insert prop {prop.toExpr this.env}: it doesn't match the type of the corresponding fvar: {← inferType expr}"
  return { this with props := this.props.insert prop expr }

meta def WidthProps.getWidthUpperBound (this : WidthProps) (ctx : PbvDecideContext) : Nat :=
  this.props.fold (fun val wTm _ =>
    val.max (wTm.getWidthUpperBound ctx)) ctx.bmcBound

/--
Traverse the local context and try to reify `Prop`s on width terms.
-/
meta def reifyPreconditions (env : TmWidthEnv)
    : MetaM WidthProps := do
  (← getLCtx).foldlM (init := { env }) fun props ldecl => do
    if let some prop ← Tm.reifyProp env (ldecl.type) then
      return ← props.pushProp prop ldecl.toExpr
    return props

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
meta def visitExprNonrec
    (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (e : Expr) :
    MetaM (WidthTms × BitVecFVarsToRevert) := do
  let te ← inferType e
  let some wExpr := getBitvecType? te
    | return (widthTms, bvs)
  let some widthTm ← Tm.reifyWidth widthTms.env wExpr
    | throwError m!"Failed to reify width expr: {wExpr}"
  let widthTms := widthTms.push widthTm
  let some fvarId := e.fvarId?
    | return (widthTms, bvs)
  return (widthTms, bvs.push fvarId widthTm)

/--
Visit an expression, collecting all widths and all bitvectors `FVars` that
correspond to individual bitvector variables.
-/
meta partial def visitExprRec (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (e : Expr) : MetaM (WidthTms × BitVecFVarsToRevert) := do
  let (widthTms, bvs) ← visitExprNonrec widthTms bvs e
  if e.isApp then
    let (f, args) := (e.getAppFn, e.getAppArgs)
    let (widthTms, bvs) ←
      args.foldlM (init := (widthTms, bvs)) fun (widthTms, bvs) arg =>
        visitExprRec widthTms bvs arg
    visitExprRec widthTms bvs f
  else
    return (widthTms, bvs)

/--
Visit the hypotheses that depend on the collected `BitVec` variables. These are
reverted into the goal when the variables are eliminated, so the `BitVec`s and
widths they mention must be collected too. Repeat until no new variables are found.
-/
meta partial def visitDependentHyps (widthTms : WidthTms) (bvs : BitVecFVarsToRevert)
    (visited : FVarIdSet := {}) : MetaM (WidthTms × BitVecFVarsToRevert) := do
  let (widthTms, newBvs, visited) ← (← getLCtx).foldlM
    (init := (widthTms, bvs, visited)) fun (widthTms, newBvs, visited) ldecl => do
      if ldecl.isImplementationDetail || visited.contains ldecl.fvarId then
        return (widthTms, newBvs, visited)
      unless ← bvs.bvs.toList.anyM (fun (fvar, _) => localDeclDependsOn ldecl fvar) do
        return (widthTms, newBvs, visited)
      let (widthTms, newBvs) ← visitExprRec widthTms newBvs ldecl.type
      return (widthTms, newBvs, visited.insert ldecl.fvarId)
  if newBvs.bvs.size == bvs.bvs.size then
    return (widthTms, newBvs)
  visitDependentHyps widthTms newBvs visited

end Veir.Meta.Tactic.PBVDecide
