module

public meta import Lean

public meta import QPFTypes.Meta.Options
public import QPFTypes.Meta.QPFExpr.Basic
public import QPFTypes.Meta.QPFExpr.FinTuple
public import QPFTypes.Theory.QPF

/-!
# QPFExpr.AddDecl

This file defines how `QPFExpr`s get added to the Lean environment.

* `QPFExpr.addDecls`: add a type function and its corresponding QPF instance
    to the environment, in both curried and uncurried forms.
* `QPFExpr.addDeclsInferringLevelParams`: convenience wrapper, which infers
    universe levels, introducing new parameters for meta-variables,
    and then calls `addDecls` with these parameters.
-/

public meta section

namespace QPFTypes
open Lean Meta Elab

namespace QPFExpr

/--
Construct a declaration and add it to the environment, at regular reducability.

If the definition is public, it's body is exposed.
This is needed, as this is used to define instances, which Lean always expects
to be exposed and types; the Lean compiler currently complains about definitions
over types whose definition is not exposed, citing a compiler limitation.
-/
private meta def addDefn (name : Name) (levelParams : List Name) (type value : Expr) :
    MetaM Declaration := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  trace[QPFTypes] "{name} : {type} :=\n{value}"
  if ← getBoolOption `QPFTypes.debug false then
    Meta.check value
    Meta.check type
    let actualType ← inferType value
    unless ← isDefEq actualType type do
      throwError "{value} {← mkHasTypeButIsExpectedMsg actualType type}"

  -- The reducibility hint is computed just like the `def` command does.
  let hints := .regular (getMaxHeight (← getEnv) value + 1)
  let decl := Declaration.defnDecl <|
    ← mkDefinitionValInferringUnsafe name levelParams type value hints
  addDecl decl (forceExpose := true)
  return decl

/--
Like `addDefn`, but registers `name` as a global instance, and compiles it.
-/
private meta def addInstanceDefn (name : Name) (levelParams : List Name) (type value : Expr) :
    MetaM Unit := do
  let decl ← addDefn name levelParams type value
  compileDecl decl
  registerInstance name .global (eval_prio default)
  -- ^^ NOTE: this also sets reducability, after the fact, which is why it's OK
  --    for `addDefn` to always use regular reducability.

/--
`q.addDecls declName levelParams deadVars` adds the qpf `q` to the environment,
with the given name and universe level parameters,
as the following 4 declarations:

```
def      $F.Uncurried ${deadVars} : TypeFun.{$u, $u} $n
instance $F.Uncurried.instQPF ${deadVars} : QPF ($F.Uncurried ${deadVars})
def      $F ${deadVars} : CurriedTypeFun.{$u} $n
instance $F.instQPF ${deadVars} : QPF (TypeFun.ofCurried ($F ${deadVars}))
```

Additionally, if `q.isPolynomial?` is given, there are 2 more instances:
```
instance $F.Uncurried.instIsPolynomial ${deadVars} :
    IsPolynomial ($F.Uncurried ${deadVars}) ($F.Uncurried.instQPF ${deadVars})
instance $F.instIsPolynomial ${deadVars} :
    IsPolynomial (TypeFun.ofCurried ($F ${deadVars})) ($F.instQPF ${deadVars})
```

The uncurried form is what all constructions on QPFs are stated in terms of,
while the curried form is what users expect to apply: `$F α β`.

"Dead" variables are those variables over which the QPF is not functorial,
which means they become parameters of all these definitions. Apart from these
variables, `q` must be a closed expression.
-/
meta def addDecls (q : QPFExpr u n) (declName : Name) (levelParams : List Name)
    (deadVars : Array Expr := #[]) : MetaM Unit :=
  withTraceNode `QPFTypes (fun _ => return m!"adding declarations for {declName}") do
    let uncurriedName := declName ++ `Uncurried
    let uncurriedInstName := uncurriedName ++ `instQPF
    let uncurriedPolyInstName := uncurriedName ++ `instIsPolynomial
    let instName := declName ++ `instQPF
    let polyInstName := declName ++ `instIsPolynomial
    let levels := levelParams.map Level.param
    let n := toExpr n

    /- `def $declName.Uncurried $deadVars* : TypeFun.{u, u} $n := $(q.typefun)` -/
    discard <| addDefn uncurriedName levelParams
      (← mkForallFVars deadVars (mkApp (mkConst ``TypeFun [u, u]) n))
      (← mkLambdaFVars deadVars q.typefun)

    /- `instance $declName.Uncurried.instQPF $deadVars* :
          QPF ($declName.Uncurried $deadVars*) := $(q.qpf)` -/
    let uncurried := mkAppN (mkConst uncurriedName levels) deadVars
    addInstanceDefn uncurriedInstName levelParams
      (← mkForallFVars deadVars (mkApp2 (mkConst ``QPF [u, u]) n uncurried))
      (← mkLambdaFVars deadVars q.qpf)

    /- `def $declName $deadVars* : CurriedTypeFun.{u} $n :=
          TypeFun.curry ($declName.Uncurried $deadVars*)` -/
    discard <| addDefn declName levelParams
      (← mkForallFVars deadVars (mkApp (mkConst ``CurriedTypeFun [u]) n))
      (← mkLambdaFVars deadVars (mkApp2 (mkConst ``TypeFun.curry [u]) n uncurried))

    /- `instance $declName.instQPF $deadVars* :
          QPF (TypeFun.ofCurried ($declName $deadVars*)) := QPF.instOfCurriedCurry`
    -/
    let ofCurried := mkApp2 (mkConst ``TypeFun.ofCurried [u]) n <|
      mkAppN (mkConst declName levels) deadVars
    addInstanceDefn instName levelParams
      (← mkForallFVars deadVars (mkApp2 (mkConst ``QPF [u, u]) n ofCurried))
      (← mkLambdaFVars deadVars <|
        mkApp3 (mkConst ``QPF.instOfCurriedCurry [u]) n uncurried
          (mkAppN (mkConst uncurriedInstName levels) deadVars))

    if let some isPolynomial := q.isPolynomial? then
      /- `instance $declName.Uncurried.instIsPolynomial $deadVars* :
          IsPolynomial ($declName.Uncurried $deadVars*)
            ($declName.Uncurried.instQPF $deadVars*) := $(q.isPolynomial?)`
      -/
      let uncurriedInst := mkAppN (mkConst uncurriedInstName levels) deadVars
      addInstanceDefn uncurriedPolyInstName levelParams
        (← mkForallFVars deadVars
          (mkApp3 (mkConst ``QPF.IsPolynomial [u]) n uncurried uncurriedInst))
        (← mkLambdaFVars deadVars isPolynomial)

      /- `instance $declName.instIsPolynomial $deadVars* :
              IsPolynomial (TypeFun.ofCurried ($declName $deadVars*))
                ($declName.instQPF $deadVars*) :=
            QPF.IsPolynomial.instOfCurriedCurry`
      -/
      let uncurriedPolyInst := mkAppN (mkConst uncurriedPolyInstName levels) deadVars
      let inst := mkAppN (mkConst instName levels) deadVars
      addInstanceDefn polyInstName levelParams
        (← mkForallFVars deadVars
          (mkApp3 (mkConst ``QPF.IsPolynomial [u]) n ofCurried inst))
        (← mkLambdaFVars deadVars <|
          mkApp4 (mkConst ``QPF.IsPolynomial.instOfCurriedCurry [u]) n uncurried
            uncurriedInst uncurriedPolyInst)

/--
Infer the universe level parameters that a qpf should be added to the
environment with, by turning every universe metavariable that is still
unassigned into a universe parameter.

Returns those parameters, together with `q` with its universe level
instantiated, ready to be passed on to `addDecls`.

The `deadVars` are as in `addDecls`,
and `scopeLevelNames` as in `addDeclsInferringLevelParams`.
-/
private meta def inferLevelParams (q : QPFExpr u n) (deadVars : Array Expr)
    (scopeLevelNames : List Name) :
    TermElabM (List Name × (u' : Level) × QPFExpr u' n) := do
  /-
  Note that we abstract over the dead variables first, so that metavariables
  occurring only in *their* types are covered as well. The abstracted
  expressions are used only to collect the parameters, since `addDecls` redoes
  the abstraction itself; it picks up the assignments made here when it
  instantiates.
  -/
  let typefun ← Term.levelMVarToParam (← instantiateMVars (← mkLambdaFVars deadVars q.typefun))
  let qpf ← Term.levelMVarToParam (← instantiateMVars (← mkLambdaFVars deadVars q.qpf))
  let isPolynomial? ← q.isPolynomial?.mapM fun p => do
    Term.levelMVarToParam (← instantiateMVars (← mkLambdaFVars deadVars p))
  let u' ← instantiateLevelMVars u
  let usedParams :=
    let s := collectLevelParams {} typefun
    let s := collectLevelParams s qpf
    let s := isPolynomial?.elim s (collectLevelParams s)
    (collectLevelParams s (.sort u')).params
  let levelParams? := sortDeclLevelParams scopeLevelNames (← Term.getLevelNames) usedParams
  let levelParams ← match levelParams? with
    | .error msg => throwError msg
    | .ok levelParams => pure levelParams
  return (levelParams,
    ⟨u', { typefun := q.typefun, qpf := q.qpf, isPolynomial? := q.isPolynomial? }⟩)

/--
Wrapper around `addDecls`, which infers universe level parameters from the
given expressions.

The `scopeLevelNames` are the universe parameters that were introduced by the
`universe` command, as opposed to those that were bound by the declaration
itself; these are allowed to go unused.
-/
meta def addDeclsInferringLevelParams (q : QPFExpr u n) (declName : Name)
    (deadVars : Array Expr := #[]) (scopeLevelNames : List Name := []) : TermElabM Unit := do
  let (levelParams, ⟨_, q⟩) ← inferLevelParams q deadVars scopeLevelNames
  q.addDecls declName levelParams deadVars

end QPFExpr

end QPFTypes

end
