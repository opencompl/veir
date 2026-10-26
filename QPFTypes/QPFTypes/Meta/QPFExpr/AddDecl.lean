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
-/

public meta section

namespace QPFTypes
open Lean Meta Elab

namespace QPFExpr

/--
Construct a declaration and add it to the environment, at regular reducability.

If the definition is public, its body is exposed.
This is needed, as this is used to define instances, which Lean always expects
to be exposed, and types, which similarly need to be exposed as per a current
compiler limitation Lena complains about when defining a function over a type
whose definition is not exposed.

See `addInstanceDefn` for justification why we only set regular reducability,
even for definitions that will be registered as an instance.
-/
private meta def addDefn (name : Name) (levelParams : List Name) (type value : Expr) :
    MetaM Declaration := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  trace[QPFTypes] "Defining {name} : {type} :=\n{value}"
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
Like `addDefn`, but registers `name` as an instance (with the given attribute
kind, i.e., global, scoped or local), and compiles it.

Note that registering `name` as an instance also sets the reducability of the
previously added declaration to `instanceReducible`; which is why we needn't
bother setting a different reducability for instances in `addDefn`.
-/
private meta def addInstanceDefn (attrKind : AttributeKind) (name : Name)
    (levelParams : List Name) (type value : Expr) : MetaM Unit := do
  let decl ← addDefn name levelParams type value
  compileDecl decl
  registerInstance name attrKind (eval_prio default)

/--
`q.addDecls F levelParams deadVars` adds the qpf `q` to the environment,
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

If a definition with the given name `F` already exists, it will not be redefined.
Rather, the existing definition of `F` is asserted to be def-eq to the definition
of `F` that would've been generated here, and the generated QPF instance on `F`
is still added to the environment.
If the existing definition of `F` is *not* def-eq, an error will be thrown.

The uncurried form is what all constructions on QPFs are stated in terms of,
while the curried form is what users expect to apply: `$F α β`.

"Dead" variables are those variables over which the QPF is not functorial,
which means they become parameters of all these definitions. Apart from these
variables, `q` must be a closed expression.

The instances are registered with the given `attrKind` (global, by default).
The definitions themselves are always added to the environment.
-/
meta def addDecls (q : QPFExpr n) (declName : Name) (levelParams : List Name)
    (deadVars : Array Expr := #[]) (attrKind : AttributeKind := .global) : MetaM Unit :=
  let decl := (.const declName (levelParams.map Level.param))
  withTraceNode `QPFTypes (fun _ => return m!"adding QPF declarations for '{decl}'") do
    let uncurriedName := declName ++ `Uncurried
    let uncurriedInstName := uncurriedName ++ `instQPF
    let uncurriedPolyInstName := uncurriedName ++ `instIsPolynomial
    let instName := declName ++ `instQPF
    let polyInstName := declName ++ `instIsPolynomial
    let levels := levelParams.map Level.param
    let n := toExpr n
    -- Typefun.curry requires a homogeneous QPF
    let q ← q.unifyLevels
    let u := q.domLevel

    trace[QPFTypes] "Using level parameters: {levelParams}"
    trace[QPFTypes] "Using dead variables: {deadVars}"

    /- `def $declName.Uncurried $deadVars* : TypeFun.{u, u} $n := $(q.typefun)` -/
    discard <| addDefn uncurriedName levelParams
      (← mkForallFVars deadVars (mkApp (mkConst ``TypeFun [u, u]) n))
      (← mkLambdaFVars deadVars q.typefun)

    /- `instance $declName.Uncurried.instQPF $deadVars* :
          QPF ($declName.Uncurried $deadVars*) := $(q.qpf)` -/
    let uncurried := mkAppN (mkConst uncurriedName levels) deadVars
    addInstanceDefn attrKind uncurriedInstName levelParams
      (← mkForallFVars deadVars (mkApp2 (mkConst ``QPF [u, u]) n uncurried))
      (← mkLambdaFVars deadVars q.qpf)

    -- Only add `$declName` itself, if it does not exist yet
    /- `def $declName $deadVars* : CurriedTypeFun.{u} $n :=
            TypeFun.curry ($declName.Uncurried $deadVars*)` -/
    let Fvalue ← mkLambdaFVars deadVars (mkApp2 (mkConst ``TypeFun.curry [u]) n uncurried)
    if (← getEnv).contains declName then
      -- `$declName` does exist, so assert that it's definition is def-eq to
      -- what we would have generated
      unless ← isDefEq decl Fvalue do
        throwError "\
          While showing that '{decl}' is a QPF, failed to unify:{indentExpr decl}\n\
            with: {indentExpr Fvalue}\
        "
    else
      discard <| addDefn declName levelParams
        (← mkForallFVars deadVars (mkApp (mkConst ``CurriedTypeFun [u]) n))
        Fvalue

    /- `instance $declName.instQPF $deadVars* :
          QPF (TypeFun.ofCurried ($declName $deadVars*)) := QPF.instOfCurriedCurry`
    -/
    let ofCurried := mkApp2 (mkConst ``TypeFun.ofCurried [u]) n <|
      mkAppN (mkConst declName levels) deadVars
    addInstanceDefn attrKind instName levelParams
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
      addInstanceDefn attrKind uncurriedPolyInstName levelParams
        (← mkForallFVars deadVars
          (mkApp3 (mkConst ``QPF.IsPolynomial [u, u]) n uncurried uncurriedInst))
        (← mkLambdaFVars deadVars isPolynomial)

      /- `instance $declName.instIsPolynomial $deadVars* :
              IsPolynomial (TypeFun.ofCurried ($declName $deadVars*))
                ($declName.instQPF $deadVars*) :=
            QPF.IsPolynomial.instOfCurriedCurry`
      -/
      let uncurriedPolyInst := mkAppN (mkConst uncurriedPolyInstName levels) deadVars
      let inst := mkAppN (mkConst instName levels) deadVars
      addInstanceDefn attrKind polyInstName levelParams
        (← mkForallFVars deadVars
          (mkApp3 (mkConst ``QPF.IsPolynomial [u, u]) n ofCurried inst))
        (← mkLambdaFVars deadVars <|
          mkApp4 (mkConst ``QPF.IsPolynomial.instOfCurriedCurry [u]) n uncurried
            uncurriedInst uncurriedPolyInst)

end QPFExpr
end QPFTypes
end
