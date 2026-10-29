module

public meta import Lean
public import QPFTypes.Theory.QPF.Cofix.WithBot
public import QPFTypes.Meta.ProductiveBy.SimpLemmas

/-!
# `productive_by_intro` tactic
-/

namespace QPFTypes.Codef

universe u

/-- `ProductiveByMotive extra P` is just `P`. On a goal `P = CofixWithBot.HasNoBot (f.__partial xs)`,
it instructs `productive_by_intro` to add `extra` as a disjunct to the motive. This is how
`codef ... with_motive t productive_by tac` passes the translated `t` on. -/
@[expose] public def ProductiveByMotive {β : Sort u} (_extra : β → Prop) (P : Prop) : Prop := P

end QPFTypes.Codef

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

/-- If `p` is `CofixWithBot.ofCofix x`, the total value `x`. -/
def ofCofixArg? (p : Expr) : Option Expr :=
  if p.isAppOfArity ``QPF.CofixWithBot.ofCofix 5 then some p.appArg! else none

/-- `∃ ys, z = c args`, where `args` is `ps` with the changing (non-`fixed`) positions
replaced by the bound variables `ys`. Where `ps` passes a total value `ofCofix x` (to a
possibly-partial parameter of `c`), the variable is total as well, and passed as `ofCofix y`. -/
partial def mkExistsEq (z c : Expr) (ps : Array Expr) (fixed : Array Bool) (i : Nat := 0)
    (args : Array Expr := #[]) : MetaM Expr := do
  if h : i < ps.size then
    if fixed[i]! then return ← mkExistsEq z c ps fixed (i + 1) (args.push ps[i])
    let .forallE n d _ _ ← whnf (← inferType (mkAppN c args))
      | throwError "productive_by_intro: unexpected type of{indentExpr c}"
    let (d, wrap) ← match ofCofixArg? ps[i] with
      | some x => pure (← inferType x, mkApp ps[i].appFn!)
      | none => pure (d, id)
    withLocalDeclD n d fun y => do
      let body ← mkExistsEq z c ps fixed (i + 1) (args.push (wrap y))
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

/-- Split a hypothesis `h : P₀ ∨ .. ∨ Pₙ` into `n + 1` goals, with hypotheses `h : Pᵢ`. -/
def splitOr (g : MVarId) (h : FVarId) : Nat → MetaM (Array (MVarId × FVarId))
  | 0 => return #[(g, h)]
  | n + 1 => do
    let #[l, r] ← g.cases h
      | throwError "productive_by_intro: failed to split the motive"
    return #[(l.mvarId, l.fields[0]!.fvarId!)] ++
      (← splitOr r.mvarId r.fields[0]!.fvarId! n)

/-- Destruct the existentials of a hypothesis `h : ∃ ys, z = e`, naming the witnesses after the
binders, and substitute `z` away. If `h` is not of this form, as much as possible is done. -/
partial def destructExistsEq (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← instantiateMVars (← h.getType))
  if ty.isAppOfArity ``Exists 2 then
    let n := match ty.appArg! with
      | .lam n .. => n
      | _ => `y
    let #[s] ← g.cases h #[{ varNames := [n] }]
      | throwError "productive_by_intro: failed to destruct the motive"
    destructExistsEq s.mvarId s.fields[1]!.fvarId!
  else
    try subst g h catch _ => pure g

/--
`productive_by_intro` sets up a coinductive productivity proof, on a goal
`CofixWithBot.HasNoBot (f.__partial xs)`. `codef ... productive_by tac` runs it before `tac`.

It applies `CofixWithBot.HasNoBot.coinduct` with the motive
`fun z => ∃ ys, z = f.__partial xs[ys]`, where `ys` replaces those arguments which are
changed by some recursive call of `f.__partial`. Total values `ofCofix x` passed to
possibly-partial parameters are replaced by `ofCofix y`, for a total `y`. It then introduces `z` and the motive,
unfolds `f.__partial` in the latter, and destructs it, substituting `z` away. The
arguments `ys` are named after the parameters of `f`, and replace the original `xs`. Finally,
it cleans up the goal with `simp only [qpf_productive_by]`.

If the goal is wrapped in `ProductiveByMotive extra₁ (.. (ProductiveByMotive extraₙ _))`
(see `codef ... with_motive`), the motive is instead `fun z => (∃ ys, ..) ∨ extra₁ z ∨ .. ∨
extraₙ z`, and there is one goal per disjunct: `rec` for the first, and `with_motive_i` for
`extraᵢ`. The latter are expected to be of the form `fun z => ∃ ws, z = e`; their existentials
are destructed, substituting `z` away, but `f.__partial` is not unfolded in them.
-/
syntax (name := productiveByIntro) "productive_by_intro" : tactic

open Elab in
@[tactic productiveByIntro]
def evalProductiveByIntro : Tactic.Tactic := fun _ => Tactic.withMainContext do
  let goal ← Tactic.getMainGoal
  let mut tgt := (← instantiateMVars (← goal.getType)).cleanupAnnotations
  let mut extras := #[]
  while tgt.isAppOfArity ``ProductiveByMotive 3 do
    extras := extras.push tgt.appFn!.appArg!
    tgt := tgt.appArg!.cleanupAnnotations
  let some p := (if tgt.isAppOf ``QPF.CofixWithBot.HasNoBot then some tgt.appArg! else none)
    | throwError "productive_by_intro: expected a goal of the form \
        `CofixWithBot.HasNoBot (f.__partial ..)`, got{indentExpr tgt}"
  let c := p.getAppFn
  let .const cName _ := c
    | throwError "productive_by_intro: expected an application of a constant{indentExpr p}"
  let ps := p.getAppArgs
  let fixed ← fixedParams cName ps.size
  let motive ← withLocalDeclD `z (← inferType p) fun z => do
    let ds := #[← mkExistsEq z c ps fixed] ++ extras.map (·.beta #[z])
    mkLambdaFVars #[z] (ds.pop.foldr mkOr ds.back!)
  let ws := (ps.zip fixed).filterMap fun (x, b) =>
    if b then none else some ((ofCofixArg? x).getD x)
  let mp := motive.beta #[p]
  let init ← if extras.isEmpty then proveExistsEq mp p ws.toList else
    pure <| mkApp3 (mkConst ``Or.inl) mp.appFn!.appArg! mp.appArg!
      (← proveExistsEq mp.appFn!.appArg! p ws.toList)
  let coinduct ← mkAppM ``QPF.CofixWithBot.HasNoBot.coinduct #[motive]
  let .forallE _ stepTy _ _ ← whnfR (← inferType coinduct)
    | throwError "productive_by_intro: unexpected type of `CofixWithBot.HasNoBot.coinduct`"
  let step ← mkFreshExprSyntheticOpaqueMVar (← Core.betaReduce stepTy) (← goal.getTag)
  goal.assign (mkApp3 coinduct step p init)
  let (_, g) ← step.mvarId!.intro1
  let (h, g) ← g.intro1
  let cases ← splitOr g h extras.size
  let (g, h) := cases[0]!
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
  let mut goals := #[← subst g h]
  for (g', h') in cases.extract 1 cases.size do
    let (g', _) ← g'.tryClearMany' (ws.filterMap (·.fvarId?))
    goals := goals.push (← destructExistsEq g' h')
  unless extras.isEmpty do
    goals[0]!.setTag `rec
    for i in [1:goals.size] do
      goals[i]!.setTag (.mkSimple s!"with_motive_{i}")
  -- Clean up the types in the goals, e.g. `∀ z : (TypeVec.nil ::: α ::: PT) 0, ..`.
  let rest := (← Tactic.getGoals).drop 1
  let mut result := #[]
  for g' in goals do
    Tactic.setGoals [g']
    Tactic.evalTactic (← `(tactic| try simp only [qpf_productive_by]))
    result := result ++ (← Tactic.getUnsolvedGoals)
  Tactic.setGoals (result.toList ++ rest)
