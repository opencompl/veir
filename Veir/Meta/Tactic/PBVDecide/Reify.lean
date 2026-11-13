module

public meta import Veir.Meta.Tactic.PBVDecide.Config
public meta import Veir.Meta.Tactic.PBVDecide.Basic

open Lean Meta Std

namespace Veir.Meta.Tactic.PBVDecide

meta def Expr.isNat (e : Expr) : Bool := e.isConstOf ``Nat

public meta def getBitvecType? (e : Expr) : Option Expr :=
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
public meta partial def Tm.reifyWidth (e : Expr) : ReifyM WidthTm := do
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
meta def reifyPreconditions (visitedFvars : HashMap FVarId LocalDecl) : ReifyM Unit := do
  (← getLCtx).forM fun ldecl => do
    unless visitedFvars.contains ldecl.fvarId do
      if let some prop ← Tm.reifyProp (ldecl.type) then
        pushProp prop ldecl.toExpr

/--
Given an expression, if it is of `BitVec w` type then create a term `Tm` for the
width `w`. If it is also an FVar then it is a variable, and hence has to be
added to the set of FVars to be reverted. A let-bound FVar is not a variable:
its value is returned instead, for the caller to visit.
-/
meta def visitExprNonrec (e : Expr) : ReifyM (Option Expr) := do
  let te ← inferType e
  let some wExpr := getBitvecType? te | return none
  let widthTm ← Tm.reifyWidth wExpr
  modify fun s => { s with widthTms := s.widthTms.insert widthTm }
  if let some fvarId := e.fvarId? then
    if let some value ← fvarId.getValue? then
      return value
    else
      modify fun s => { s with bvs := s.bvs.insert fvarId widthTm }
  return none
/--
Visit an expression, collecting all widths and all bitvectors `FVars` that
correspond to individual bitvector variables.
-/
meta partial def visitExprRec (e : Expr) : ReifyM Unit := do
  if let some e' ← visitExprNonrec e then
    visitExprRec e'
  if e.isApp then
    let (f, args) := (e.getAppFn, e.getAppArgs)
    -- `Nat` values that may be built from widths without appearing as the `w`
    -- of a `BitVec w`. They are reified separately by `reifyValues`.
    -- `Nat` shift amounts and bit indices are pushed as shifts by
    -- `BitVec.ofNatClamp o n`, which is translated like `BitVec.ofNat o n`.
    let isBvNatShift (α β : Expr) := (getBitvecType? α).isSome && Expr.isNat β
    let value? := match f, args with
      | .const ``BitVec.extractLsb' _, #[_, start, _, _] => some start
      | .const ``BitVec.ofNat _, #[_, n] => some n
      | .const ``BitVec.twoPow _, #[_, n] => some n
      | .const ``HShiftLeft.hShiftLeft _, #[α, β, _, _, _, n]
      | .const ``HShiftRight.hShiftRight _, #[α, β, _, _, _, n] =>
        if isBvNatShift α β then some n else none
      | .const ``BitVec.shiftLeft _, #[_, _, n]
      | .const ``BitVec.ushiftRight _, #[_, _, n]
      | .const ``BitVec.sshiftRight _, #[_, _, n]
      | .const ``BitVec.getLsbD _, #[_, _, n] => some n
      | _, _ => none
    if let some v := value? then
      modify fun s => { s with valueCands := s.valueCands.insert v }
    args.forM fun arg =>
      visitExprRec arg
    visitExprRec f
  else if let some (α, β) := e.arrow? then
    visitExprRec α
    visitExprRec β

/--
Collect the local declarations to revert into the goal: those that depend on the
collected `BitVec` variables, and those mentioning a `BitVec` whose width shares a
width variable or atom with the widths collected so far. The `BitVec`s and widths
they mention are collected too. Repeat until no new variables or widths are found.
-/
meta partial def getBvLocalDecls (visited : HashMap FVarId LocalDecl := {}) : ReifyM (HashMap FVarId LocalDecl) := do
  let oldState := (← get)
  let visited ← (← getLCtx).foldlM
    (init := visited) fun visited ldecl => do
      if ldecl.isImplementationDetail || visited.contains ldecl.fvarId then
        return visited
      if ← (← get).dependsOnBvs ldecl then
        visitExprRec ldecl.type
        return visited.insert ldecl.fvarId ldecl
      else
        -- Run reification on the local decl to extract width terms
        let (_, reified) ← (visitExprRec (ldecl.type)).run { (← get) with widthTms := {} }
        let newAtoms := reified.widthTms.atoms
        let oldAtoms := (← get).widthTms.atoms
        -- Only if the term contains widths variables which also exist in the main goal
        -- then it should be reverted into the goal and translated
        if (newAtoms.inter oldAtoms).size > 0 then
          modify fun s => { reified with widthTms := s.widthTms.union reified.widthTms }
          return visited.insert ldecl.fvarId ldecl
        else
          return visited
  if oldState.bvs.size != (← get).bvs.size || oldState.widthTms.size != (← get).widthTms.size then
    return ← getBvLocalDecls visited
  return visited

/--
Reify the `Nat` values collected in `valueCands` as width terms, keeping only
those built from the widths of the `BitVec`s (and at least one of them). A kept
value is given a mask like any other width, so that `BitVec.ofNat o v` can be
translated into the `cpop` of its mask. The others are left untouched: they are
not given a mask, and hence do not need to be bounded by the blast width.
-/
meta def reifyValues : ReifyM Unit := do
  -- The atoms of the widths, and of the preconditions, which are given masks too
  let widthAtoms := (← get).props.fold (init := (← get).widthTms.atoms)
    fun acc p _ => acc.union p.propAtoms
  for v in (← get).valueCands do
    -- Reify on a copy of the state, discarding the new atoms of rejected values.
    let (vTm, reified) ← (Tm.reifyWidth v).run (← get)
    let atoms := vTm.atoms
    if !atoms.isEmpty && atoms.all widthAtoms.contains then
      set { reified with widthTms := reified.widthTms.insert vTm }

/--
Reify the goal: collect the widths of the `BitVec`s in the goal and in the
hypotheses that depend on them, and the props on widths in the local context.
Returns the local declarations to revert into the goal.
-/
public meta def reifyWidths (g : MVarId) : ReifyM (HashMap FVarId LocalDecl) := g.withContext do
  -- Find `BitVec`s and reify their widths
  visitExprRec (← g.getType)
  -- Find `BitVec`s in the hypotheses that will be reverted along with them
  let ldecls ← getBvLocalDecls
  -- Traverse the context to find props on widths (preconditions)
  reifyPreconditions ldecls
  -- Reify the `Nat` values which are built from the widths
  reifyValues
  return ldecls

end Veir.Meta.Tactic.PBVDecide
