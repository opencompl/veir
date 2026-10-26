module

public meta import Lean
public import QPFTypes.Theory.QPF.Cofix.WithBot

/-!
# `productive_by_intro` tactic
-/
public meta section

namespace QPFTypes.Codef

open Lean Meta

/-- Collect the argument lists of all (maximal) applications of `c` in `e`. -/
partial def collectCalls (c : Name) (e : Expr) : StateM (Array (Array Expr)) Unit := do
  match e with
  | .app .. =>
    let fn := e.getAppFn
    if fn.isConstOf c then modify (·.push e.getAppArgs) else collectCalls c fn
    e.getAppArgs.forM (collectCalls c)
  | .const n _ => if n == c then modify (·.push #[])
  | .lam _ d b _ | .forallE _ d b _ => do collectCalls c d; collectCalls c b
  | .letE _ t v b _ => do collectCalls c t; collectCalls c v; collectCalls c b
  | .mdata _ e | .proj _ _ e => collectCalls c e
  | _ => pure ()

/-- For each of the first `arity` parameters of `declName`, whether all recursive calls in
its unfolding equation pass that parameter on unchanged. Parameters whose type depends on a
changing parameter are considered changing as well. -/
def fixedParams (declName : Name) (arity : Nat) : MetaM (Array Bool) := do
  let some eqn ← getUnfoldEqnFor? declName
    | throwError "productive_by_intro: no unfolding equation for `{.ofConstName declName}`"
  forallTelescope (← inferType (← mkConstWithFreshMVarLevels eqn)) fun _ eq => do
    let some (_, lhs, rhs) := eq.eq?
      | throwError "productive_by_intro: unexpected unfolding equation{indentExpr eq}"
    let params := lhs.getAppArgs
    let ((), calls) := (collectCalls declName rhs).run #[]
    let mut fixed := Array.replicate arity true
    for i in [:arity] do
      fixed := fixed.set! i <| i < params.size &&
        calls.all fun args => i < args.size && args[i]! == params[i]!
    forallBoundedTelescope (← inferType lhs.getAppFn) arity fun zs _ => do
      let mut fixed := fixed
      for j in [:zs.size] do
        let ty ← inferType zs[j]!
        if fixed[j]! && (List.range j).any fun i => !fixed[i]! && ty.containsFVar zs[i]!.fvarId!
        then fixed := fixed.set! j false
      return fixed

/-- `∃ ys, z = c args`, where `args` is `ps` with the changing (non-`fixed`) positions
replaced by the bound variables `ys`. -/
partial def mkExistsEq (z c : Expr) (ps : Array Expr) (fixed : Array Bool) (i : Nat := 0)
    (args : Array Expr := #[]) : MetaM Expr := do
  if h : i < ps.size then
    if fixed[i]! then return ← mkExistsEq z c ps fixed (i + 1) (args.push ps[i])
    let .forallE n d _ _ ← whnf (← inferType (mkAppN c args))
      | throwError "productive_by_intro: unexpected type of{indentExpr c}"
    withLocalDeclD n d fun y => do
      let body ← mkExistsEq z c ps fixed (i + 1) (args.push y)
      mkAppM ``Exists #[← mkLambdaFVars #[y] body]
  else
    mkEq z (mkAppN c args)

/-- Prove `e = ∃ ys, p = c args` using the witnesses `ws` and `rfl`. -/
partial def proveExistsEq (e p : Expr) : List Expr → MetaM Expr
  | w :: ws => do
    let .app (.app (.const ``Exists lvls) ty) pred := e
      | throwError "productive_by_intro: expected an existential{indentExpr e}"
    let h ← proveExistsEq (pred.beta #[w]) p ws
    return mkApp4 (.const ``Exists.intro lvls) ty pred w h
  | [] => mkEqRefl p

/--
`productive_by_intro` sets up a coinductive productivity proof, on a goal
`CofixWithBot.HasNoBot (f.__partial xs)`. `codef ... productive_by tac` runs it before `tac`.

It applies `CofixWithBot.HasNoBot.coinduct` with the motive
`fun z => ∃ ys, z = f.__partial xs[ys]`, where `ys` replaces those arguments which are
changed by some recursive call of `f.__partial`. It then introduces `z` and the motive,
unfolds `f.__partial` in the latter, and destructs it, substituting `z` away. The
arguments `ys` are named after the parameters of `f`, and replace the original `xs`.
-/
syntax (name := productiveByIntro) "productive_by_intro" : tactic

open Elab in
@[tactic productiveByIntro]
def evalProductiveByIntro : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let tgt := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let some p := (if tgt.isAppOf ``QPF.CofixWithBot.HasNoBot then some tgt.appArg! else none)
    | throwError "productive_by_intro: expected a goal of the form \
        `CofixWithBot.HasNoBot (f.__partial ..)`, got{indentExpr tgt}"
  let c := p.getAppFn
  let .const cName _ := c
    | throwError "productive_by_intro: expected an application of a constant{indentExpr p}"
  let ps := p.getAppArgs
  let fixed ← fixedParams cName ps.size
  let motive ← withLocalDeclD `z (← inferType p) fun z => do
    mkLambdaFVars #[z] (← mkExistsEq z c ps fixed)
  let ws := (ps.zip fixed).filterMap fun (x, b) => if b then none else some x
  let init ← proveExistsEq (motive.beta #[p]) p ws.toList
  let coinduct ← mkAppM ``QPF.CofixWithBot.HasNoBot.coinduct #[motive]
  let .forallE _ stepTy _ _ ← whnfR (← inferType coinduct)
    | throwError "productive_by_intro: unexpected type of `CofixWithBot.HasNoBot.coinduct`"
  let step ← mkFreshExprSyntheticOpaqueMVar (← Core.betaReduce stepTy) (← goal.getTag)
  goal.assign (mkApp3 coinduct step p init)
  let (_, g) ← step.mvarId!.intro1
  let (h, g) ← g.intro1
  -- Unfold `f.__partial` in the motive only, not in the goal.
  let some (h, g) ← g.withContext do
      let r ← unfold (← instantiateMVars (← h.getType)) cName
      applySimpResultToLocalDecl g h r (mayCloseGoal := false)
    | throwError "productive_by_intro: unexpected closed goal"
  let (g, _) ← g.tryClearMany' (ws.filterMap (·.fvarId?))
  -- Destruct the existentials, and substitute along the equation.
  let names ← forallBoundedTelescope (← inferType c) ps.size fun zs _ =>
    (zs.zip fixed).filterMapM fun (x, b) =>
      if b then pure none else some <$> x.fvarId!.getUserName
  let mut g := g
  let mut h := h
  for n in names do
    let #[s] ← g.cases h #[{ varNames := [n] }]
      | throwError "productive_by_intro: failed to destruct the motive"
    g := s.mvarId
    h := s.fields[1]!.fvarId!
  Tactic.replaceMainGoal [← subst g h]
