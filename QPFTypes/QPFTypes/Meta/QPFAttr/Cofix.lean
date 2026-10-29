module

public meta import Lean

public import QPFTypes.Theory.QPF.Cofix.WithBot
public import QPFTypes.Theory.QPF.Cofix.Order

/-!
# The `@[qpf]` attribute on `Cofix` types

This is the code path of `@[qpf]` for definitions whose body is, at the root, an application
of `QPF.Cofix`, e.g.,
```
@[qpf] def Stream (α : Type) : Type :=
  Cofix (@TypeFun.ofCurried 2 StreamF) #t[α]
```
Such definitions are not type functions to derive a `QPF` instance for (`Cofix` always gives an
uncurried type function, rather than the curried ones the main code path looks for), but
coinductive types, for which we define the possibly-partial analogue, via `CofixWithBot`
(and, if the functor is polynomial, a `CCPO` instance for it, via `deriving CCPO`):
```
def Stream.__partial (α : Type) : Type :=
  CofixWithBot (@TypeFun.ofCurried 2 StreamF) #t[α]
```
-/

public meta section

namespace QPFTypes.QPFAttr
open Lean Meta

/-- The suffix of the possibly-partial analogue `T.__partial` of a coinductive type `T`. -/
def partialSuffix : String := "__partial"

/-- Whether the body of the definition `declName`, under its leading lambdas, is an
application of `QPF.Cofix`. -/
def isCofixDef (declName : Name) : MetaM Bool := do
  let some value := (← getConstInfo declName).value? (allowOpaque := false)
    | return false
  lambdaTelescope value fun _ body =>
    return body.isAppOfArity ``QPF.Cofix 4

/--
Given a definition `T := fun xs => @Cofix n F q α`, add the definition
`T.__partial := fun xs => @CofixWithBot n F q α`, with the same type and universe parameters.

If `F` is polynomial, `T.__partial` additionally gets a `CCPO` instance, as if it were defined
with `deriving CCPO`, so that `partial_fixpoint` can define functions into it.
-/
def addPartialCofixType (declName : Name) : MetaM Unit := do
  let info ← getConstInfoDefn declName
  let (value, isPolynomial) ← lambdaTelescope info.value fun xs body => do
    unless body.isAppOfArity ``QPF.Cofix 4 do
      throwError "@[qpf]: expected the body of `{.ofConstName declName}` to be an \
          application of `Cofix`, got{indentExpr body}"
    let lvls := body.getAppFn.constLevels!
    let args := body.getAppArgs
    let body' := mkAppN (.const ``QPF.CofixWithBot lvls) args
    -- `CofixWithBot F α` is a `CCPO` whenever `F` is polynomial.
    let u := lvls[0]!
    let isPolynomial ← synthInstance? <|
      mkApp3 (.const ``QPF.IsPolynomial [u, u]) (mkNatAdd args[0]! (mkNatLit 1)) args[1]! args[2]!
    return (← mkLambdaFVars xs body', isPolynomial.isSome)
  let value ← instantiateMVars value
  let name := declName.str partialSuffix
  trace[QPFTypes] "Defining {name} : {info.type} :=\n{value}"
  let decl := Declaration.defnDecl <| ← mkDefinitionValInferringUnsafe name info.levelParams
    info.type value (.regular (getMaxHeight (← getEnv) value + 1))
  -- Types need to be exposed, see `QPFExpr.addDefn`.
  addDecl decl (forceExpose := true)
  compileDecl decl
  if isPolynomial then
    -- The `deriving CCPO` mechanism for definitions, i.e., delta deriving.
    let view : Elab.DerivingClassView :=
      { ref := .missing, hasExpose := false, cls := mkCIdent ``Lean.Order.CCPO }
    Elab.Term.TermElabM.run' <|
      Elab.Term.processDefDeriving view (mkConst name (info.levelParams.map .param))

end QPFTypes.QPFAttr
