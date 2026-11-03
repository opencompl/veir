module

public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Basic

open Lean Meta Std

namespace Veir.Meta.Tactic.PBVDecide

meta def Expr.isNat (e : Expr) : Bool := e.isConstOf ``Nat

meta def getBitvecType? (e : Expr) : Option Expr :=
  match_expr e with
  | BitVec w => some w
  | _ => none

meta def getIdOrPush (width : Expr) : ReifyM Nat := do
  if let some id := (← get).env.idxOf? width then
    return id
  else
    modifyGet fun s => (s.env.size, { s with env := s.env.push width })

/--
Reify a `Nat` width: fvars, literals and `+` become the corresponding `Tm`
constructors, anything else becomes an opaque atom.
-/
meta partial def Tm.reifyWidth (e : Expr) : ReifyM WidthTm := do
  if let some fvarid := e.fvarId? then
    return .widthFVar (← getIdOrPush e) fvarid
  else if let some val := e.nat? then
    return .widthLit val
  else
    let op ← match_expr e with
    | HAdd.hAdd ty _ _ _ ae be =>
        let .true := Expr.isNat ty | pure none
        let a ← Tm.reifyWidth ae
        let b ← Tm.reifyWidth be
        pure <| some (widthAdd a b)
    | HSub.hSub ty _ _ _ ae be =>
        let .true := Expr.isNat ty | pure none
        let a ← Tm.reifyWidth ae
        let b ← Tm.reifyWidth be
        pure <| some (widthSub a b)
    | _ => pure none

    if let some reified := op then
      return reified
    else
      return (.widthAtom (← getIdOrPush e))

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
Reify a proposition on widths: a relation between widths, or a conjunction of
them. Returns `none` for anything else.
-/
meta partial def Tm.reifyProp (e : Expr) : ReifyM (Option WidthProp) := do
  if let some (rel, ea, eb) := matchWidthRel e then
    let wa ← Tm.reifyWidth ea
    let wb ← Tm.reifyWidth eb
    return some (rel wa wb)
  else
    match_expr e with
    | And ea eb => do
      let some pa ← Tm.reifyProp ea | return none
      let some pb ← Tm.reifyProp eb | return none
      return some (.and pa pb)
    | _ => return none

/-- Insert a `WidthProp`, checking that the type of `expr` matches the `Tm`. -/
meta def pushProp (prop : Tm .prop) (expr : Expr) : ReifyM Unit := do
  unless ← isDefEq (← inferType expr) (prop.toExpr (← get).env)
    do throwError m!"Cannot insert prop {prop.toExpr (← get).env}: it doesn't match the type of the corresponding fvar: {← inferType expr}"
  modify fun s => { s with props := s.props.insert prop expr }

/--
Traverse the local context and try to reify `Prop`s on width terms.
-/
meta def reifyPreconditions : ReifyM Unit := do
  (← getLCtx).forM fun ldecl => do
    unless ← (← get).dependsOnBvs ldecl do
      if let some prop ← Tm.reifyProp (ldecl.type) then
        pushProp prop ldecl.toExpr

/--
Given an expression, if it is of `BitVec w` type then create a term `Tm` for the
width `w`. If it is also an FVar then it is a variable, and hence has to be
added to the set of FVars to be reverted.
-/
meta def visitExprNonrec (e : Expr) : ReifyM Unit := do
  let te ← inferType e
  let some wExpr := getBitvecType? te | return
  let widthTm ← Tm.reifyWidth wExpr
  modify fun s => { s with widthTms := s.widthTms.insert widthTm }
  if let some fvarId := e.fvarId? then
    modify fun s => { s with bvs := s.bvs.insert fvarId widthTm }

/--
Visit an expression, collecting all widths and all bitvectors `FVars` that
correspond to individual bitvector variables.
-/
meta partial def visitExprRec (e : Expr) : ReifyM Unit := do
  visitExprNonrec e
  if e.isApp then
    let (f, args) := (e.getAppFn, e.getAppArgs)
    -- ExtractLsb takes a width expression as input which does not appear as a
    -- `w` in a `BitVec w` type, hence it needs to be reified separately.
    match f, args with
    | .const ``BitVec.extractLsb' _, #[_, start, _, _] =>
      let startTm ← Tm.reifyWidth start
      modify fun s => { s with widthTms := s.widthTms.insert startTm }
    | _, _ => pure ()
    args.forM fun arg =>
      visitExprRec arg
    visitExprRec f

/--
Visit the hypotheses that depend on the collected `BitVec` variables. These are
reverted into the goal when the variables are eliminated, so the `BitVec`s and
widths they mention must be collected too. Repeat until no new variables are found.
-/
meta partial def visitDependentHyps (visited : FVarIdSet := {}) : ReifyM Unit := do
  let oldBvs := (← get).bvs.size
  let visited ← (← getLCtx).foldlM
    (init := visited) fun visited ldecl => do
      if ldecl.isImplementationDetail || visited.contains ldecl.fvarId then
        return visited
      unless ← (← get).dependsOnBvs ldecl do
        return visited
      visitExprRec ldecl.type
      return visited.insert ldecl.fvarId
  if oldBvs != (← get).bvs.size then
    visitDependentHyps visited


/--
Reify the goal: collect the widths of the `BitVec`s in the goal and in the
hypotheses that depend on them, and the props on widths in the local context.
Returns the blast width, the upper bound on all the collected widths.
-/
public meta def reifyWidths (g : MVarId) : ReifyM Nat := g.withContext do
  -- Find `BitVec`s and reify their widths
  visitExprRec (← g.getType)
  -- Find `BitVec`s in the hypotheses that will be reverted along with them
  visitDependentHyps
  -- Traverse the context to find props on widths (preconditions)
  reifyPreconditions
  -- Compute the blast width
  return ((← get).props.getUpperBound (← read).bmcBound).max
          <| (← get).widthTms.getUpperBound (← read).bmcBound

end Veir.Meta.Tactic.PBVDecide
