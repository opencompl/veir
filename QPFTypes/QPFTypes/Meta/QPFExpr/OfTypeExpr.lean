module

public meta import Lean

public import QPFTypes.Meta.QPFExpr.Basic
public meta import QPFTypes.Meta.Options

public meta import QPFTypes.Meta.Basic

/-!
# The composition pipeline

This file implements ways of building a `QPFExpr` from Lean expression of types
or type functions; what is called the "composition pipeline" in [1].

## Main Definitions

* `QPFExpr.ofTypeExpr`
* `QPFExpr.ofTypeDef`

## References

[1] Alex Keizer. Implementing a definitional (co)datatype package in Lean 4,
based on quotients of polynomial functors.
https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf

-/

meta section

namespace QPFTypes
open Lean Elab Meta

/--
Gadget for marking live parameters in a QPF.

Live parameters of a type function are the only parameters for which we can take
a (co)fixpoint, meaning that these are the parameters which can be stand-ins for
(co)recursive occurrences of a (co)inductive type we want to define.

However, live parameters are more restricted than their non-live counterparts:
For example, live variables may not occur on the right-hand side of an arrow
type, or in the  index of a dependent pair type.
-/
public abbrev liveParam (α : Type u) : Type u := α

namespace QPFExpr

/--
Given a target expression `$G $a₁ ⋯ $aₘ`, find the largest prefix `$G $a₁ ⋯ $aₖ`
such that the prefix:
* does not contain any live variables, and
* is a QPF, i.e., an instance of `QPF (TypeFun.ofCurried $head)` exists.

If found, the prefix is returned, as a `QPFExpr`, together with the remaining
arguments. Otherwise, an error is thrown.
-/
private def parseApp (u : Level) (isLiveVar : FVarId → Bool) (target : Expr) :
    MetaM ((k : Nat) × QPFExpr k × Vector Expr k) := do
  let fn := target.getAppFn
  let args := target.getAppArgs
  let mut liveVarError? := none
  -- `kept` is the number of arguments that remain part of the head; we start
  -- with the largest head and peel off arguments one-by-one.
  for i in [0:args.size] do
    let kept := args.size - 1 - i
    let head := mkAppN fn (args.extract 0 kept)
    let rest := args.extract kept
    let k := rest.size

    if head.hasAnyFVar isLiveVar then
      -- Keep going; a smaller head may avoid the live variables.
      liveVarError? := some m!"\
        the head of the application still contains live variables:\
        {indentExpr head}"
      continue

    let typefun := mkApp2 (mkConst ``TypeFun.ofCurried [u]) (toExpr k) head
    trace[QPFTypes] "trying head {typefun}"
    -- `head` need not be a `k`-ary type function at all, in which case the
    -- application above is ill-typed; we simply move on to the next candidate.
    unless ← isTypeCorrect typefun do
      continue
    let some qpf ← synthInstance? (mkApp2 (mkConst ``QPF [u, u]) (toExpr k) typefun)
      | continue
    -- The head may happen to be polynomial, too; note this has to be an
    -- `IsPolynomial` for *this* `qpf` instance, not just for `typefun`.
    let isPolynomial? ←
      synthInstance? (mkApp3 (mkConst ``QPF.IsPolynomial [u, u]) (toExpr k) typefun qpf)
    return ⟨k, { domLevel := u, codLevel := u, typefun, qpf, isPolynomial? }, rest.toVector⟩

  if let some err := liveVarError? then
    throwError err
  else
    throwError "\
      failed to find a QPF in the head of the application:{indentExpr target}\n\
      note that the head, after applying it to zero or more of the arguments, \
      must be a type function with a `QPF` instance"

/-- Implementation of `ofTypeExpr` -/
partial def ofTypeExprCore (u : Level) (liveVars : Vector FVarId n) (target : Expr) :
    MetaM (QPFExpr n) :=
  withTraceNode `QPFTypes (fun _ => return m!"pipeline: {target}") do
    let isLiveVar (fvarId : FVarId) : Bool := liveVars.contains fvarId

    let target ← whnfR target
    if let some fvarIdx := target.fvarId? >>= liveVars.finIdxOf? then
      return mkProj u fvarIdx.rev

    else if !target.hasAnyFVar isLiveVar then
      return mkConstant u n target

    else if let some (A, family) := target.app2? ``Sigma then
      ofSigma A family

    else if target.isApp then
      ofApp target

    else if let .forallE _ A body _ := target then
      ofForall A body

    else
      throwError "unexpected target expression:{indentExpr target}"
where
  ofApp (target : Expr) : MetaM (QPFExpr n) := do
    let isLiveVar (fvarId : FVarId) : Bool := liveVars.contains fvarId
    let ⟨k, F, args⟩ ← parseApp u isLiveVar target
    trace[QPFTypes] "{target} is an application of {F.typefun} to {args.toList}"

    /-
    Optimization: if the application is of the form `$F $α₁ ⋯ $αₙ`, for exactly
    the live variables in order, then `F` already is the desired QPF, so we don't
    have to compose it with a tuple of projections.
    -/
    if h : k = n then
      if args.toList.mapM Expr.fvarId? == some liveVars.toList then
        trace[QPFTypes] "the application is trivial"
        return h ▸ F

    /-
    Note that the arguments have to be reversed: `TypeFun.ofCurried` reads the
    *first* curried argument from the *last* component of the type vector that
    `QPF.Comp` builds out of `Gs`.
    -/
    let Gs ← args.reverse.mapM (ofTypeExprCore u liveVars ·)
    mkComp F Gs

  /--
  Translate a (possibly dependent) function type `($binderName : $A) → $body`
  into a `QPF.Pi`.
  -/
  ofForall (A body : Expr) : MetaM (QPFExpr n) := do
    if A.hasAnyFVar (liveVars.contains ·) then
      throwError "\
        the domain of a function type may not mention live variables:{indentExpr A}\n\
        a function type is not functorial in its domain."
    unless ← isDefEq (← inferType A) (.sort u.succ) do
      throwError "\
        the domain of a function type must live in the same universe as the QPF \
        itself, but{indentExpr A}\n\
        has type{indentExpr (← inferType A)}\n\
        instead of{indentD m!"Type {u}"}"
    trace[QPFTypes] "{A} → ⋯ is a dependent product"
    mkPi u n A fun a => ofTypeExprCore u liveVars (body.instantiate1 a)

  /--
  Translate a dependent sum `($binderName : $A) × $body` into a `QPF.Sigma`.
  -/
  ofSigma (A family : Expr) : MetaM (QPFExpr n) := do
    if A.hasAnyFVar (liveVars.contains ·) then
      throwError "\
        the index type of a dependent sum may not mention live variables:\
        {indentExpr A}\n\
        a dependent sum is functorial in its summands only, not in the type it \
        is indexed by"
    unless ← isDefEq (← inferType A) (.sort u.succ) do
      throwError "\
        the index type of a dependent sum must live in the same universe as the \
        QPF itself, but{indentExpr A}\n\
        has type{indentExpr (← inferType A)}\n\
        instead of{indentD m!"Type {u}"}"
    trace[QPFTypes] "{A} × ⋯ is a dependent sum"
    mkSigma u n A fun a => ofTypeExprCore u liveVars (mkApp family a).headBeta

/--
Assert that the given QPF, represents the uncurried type function that
abstracts `target` over the given (live) free variables.

Concretely, this checks that `TypeFun.curry $q.typefun` is definitionally equal
to `fun $liveVars... => $target`.
-/
private def assertCurriedDefEq (qpf : QPFExpr n)
    (liveVars : Array FVarId) (target : Expr) : MetaM Unit := do
  let q ← qpf.unifyLevels
  let curried := mkApp2 (mkConst ``TypeFun.curry [q.domLevel]) (toExpr n) q.typefun
  let expected ← mkLambdaFVars (liveVars.map Expr.fvar) target
  unless ← withoutModifyingState (isDefEq curried expected) do
    throwError "\
      debug assertion failed, the derived type function{indentExpr curried}\n\
      is not definitionally equal to{indentExpr expected}"

/--
Call `assertCurriedDefEq` only if the `QPFTypes.debug` option is set.
-/
private def debugAssertCurriedDefEq (qpf : QPFExpr n)
    (liveVars : Array FVarId) (target : Expr) : MetaM Unit := do
  if ← getBoolOption `QPFTypes.debug false then
    qpf.assertCurriedDefEq liveVars target

/-- Throw an error if `x` is not of type `Type $u`. -/
@[inline]
private def assertLiveVarInUniverse (x : FVarId) (u : Level) : MetaM Unit := do
  let expected := Expr.sort u.succ
  let actual ← x.getType
  unless ← isDefEq actual expected do
    let expected' := mkApp (mkConst ``liveParam [u]) expected
    -- ^^ Note: `expected'` is def-eq to `expected`, but we add the liveParam
    --    here to make the error message less confusing when `actual` is also an
    --    application of `liveParam` (as it usually is).
    throwError "\
      Live parameter '{x}' \
      {← mkHasTypeButIsExpectedMsg actual expected'
        (some m!"\nNote that all live variables must live in the same universe.")
      }"

/-- Throw an error if `target` is not of type `Type $u`. -/
@[inline]
private def assertTargetInUniverse (target : Expr) (u : Level) : MetaM Unit := do
  let expected := Expr.sort u.succ
  let targetType ← inferType target
  unless ← isDefEq targetType expected do
    throwError "The expression:{indentExpr target}\n\
      {← mkHasTypeButIsExpectedMsg targetType expected
          (some m!"\nNote that the result of a QPF must live in the same type universe \
                    as it's arguments")
      }"

/--
Construct a QPFExpr from a type expression `$target : Type u` and given the free
over which to abstract. These variables are called the "live" variables, and are
required to be used in the target expression such that the resulting type
function (where these variables are abstracted) is indeed a functor.

For instance, live variables may not occur in the *domain* of an arrow type,
only in the codomain.
Furthermore, when applying a type function `G` to an argument containing a free
variable, the type function has to be a QPF (that is, an instance of
`QPF (TypeFun.ofCurried G)` must be syntesizable).
See the `liveParam` gadget for more details.

For example, `ofTypeExpr #v['α, 'β] ${ α → β }` (using pseudo quotation syntax)
throws an error, since `α` is listed as a live variable and is used on the left
side of an arrow, but `ofTypeExpr #v['β] ${ α → β }` is accepted.

Note that arity of the resulting QPF is the number of live variables.
That is, the resulting QPF is the uncurried version of the type function
`fun $liveVars... => $target`, which abstracts over the given live variables.
Converting the type function of the returned QPFExpr into a curried function,
by applying `TypeFun.curry` to it, yields an expression which is
definitionally equal to this abstracted expression.

All live variables are assumed to of type `Type v`, for the same universe `v`.
-/
public def ofTypeExpr (liveVars : Vector FVarId n) (target : Expr) :
    MetaM (QPFExpr n) :=
  try
    let u ← mkFreshLevelMVar
    liveVars.forM (assertLiveVarInUniverse · u)
    assertTargetInUniverse target u

    let qpf ← ofTypeExprCore u liveVars target
    qpf.debugAssertCurriedDefEq liveVars.toArray target
    return qpf
  catch err =>
    let liveVars := toMessageData liveVars.toList
    throwError "\
      While deriving a QPF from type expression:{indentExpr target}\n\
      With live free variables:{indentD liveVars}\n\n\
      {err.toMessageData}
      "

/--
Check whether a local declaration represents a live parameter.

That is, if the type of the given local declaration is an application of the
`liveParam` gadget, return the corresponding `FVarId`. Otherwise, return `none`.
-/
meta def LocalDecl.asLiveVar? (decl : LocalDecl) : Option FVarId :=
  if decl.type.isAppOf ``liveParam then
    some decl.fvarId
  else
    none

/--
The parameters of a QPF, separated into live and "dead" free variables.

All live variables are of type `Type $liveVarLevel`
-/
public structure QPFParams where
  liveVarLevel : Level
  liveVars : Array FVarId
  deadVars : Array FVarId

/--
Separate the parameters `fvars` of a type definition into the live parameters,
i.e., those whose type is an application of `liveParam`, and dead parameters
(i.e., the rest), returned as a `QPFParams` object.

Throws an error if a dead parameter occurs after a live parameter in the
given array of variables--all dead parameters are expected to precede the live
parameters--or if two live parameters live in different universes--all live
parameters are expected to be of type `Type u`, for some fixed universe u.
-/
public def collectLiveParams (fvars : Array FVarId) : MetaM QPFParams := do
  let mut liveVars := #[]
  let u ← mkFreshLevelMVar
  for x in fvars do
    let decl ← x.getDecl
    if let some v := LocalDecl.asLiveVar? decl then
      assertLiveVarInUniverse v u
      liveVars := liveVars.push v
    else if let some live := liveVars[0]? then
      let x := m!"{x} : {← x.getType}"
      let live := m!"{live} : {← live.getType}"
      throwError "\
        non-live parameter:{indentD x}\n\
        occurs after live parameter:{indentD live}\n\
        \n\
        Note that all non-live parameters must precede the live parameters."
  let deadVars := fvars.take (fvars.size - liveVars.size)
  return { liveVarLevel := u, liveVars, deadVars }

variable [Monad m] [MonadEnv m] [MonadError m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
              [MonadTrace m] [AddMessageContext m] [MonadOptions m] [MonadAlwaysExcept ε m]
              [MonadLiftT BaseIO m] in
/--
Run a continuation with a QPFExpr constructed from the given name of a
declaration whose definition unfolds to a type function `⋯ → Type`.

We infer which parameters are considered live by determining if their type is an
application of `liveParam`.
Throws an error if a dead (i.e., non-live) parameter occurs after a live
parameter in the type function.

The live variables are abstracted over in the resulting QPFExpr, whereas new
free variables are introduced for any dead arguments to the given type function.
The continuation is given the QPFExpr, together with an array of all newly
introduced dead variables (which may occur freely in the QPFExpr), and the
universe level parameters.

See also `ofTypeExpr` for details on how the QPFExpr is constructed.
-/
public def ofTypeDef (defn : Name)
    (k : {n : Nat} → (q : QPFExpr n) →
      (levelParams : List Name) → (deadVars : Array FVarId) → m α) : m α := withErrContext do
  let info ← getConstInfoDefn defn
  trace[QPFTypes] "Defined as: {info.value}"
  forallTelescopeReducing info.type fun fvars _type => do
    let { liveVars, deadVars, liveVarLevel := u } ← collectLiveParams (fvars.map Expr.fvarId!)
    trace[QPFTypes] "Identified:\nLive variables: {liveVars}\nDead variables: {deadVars}"

    let target := mkAppN info.value fvars
    assertTargetInUniverse target u
    let qpf ← ofTypeExprCore u ⟨liveVars, rfl⟩ target
    qpf.debugAssertCurriedDefEq liveVars target
    k qpf info.levelParams deadVars
where
  @[inline]
  withErrContext {α} (x : m α) : m α :=
    let defn := MessageData.ofConstName defn
    withTraceNode `QPFTypes (fun _ => pure m!"Building a QPF expression from definition '{defn}'") <|
      try x catch err =>
        throwError "\
          While deriving a QPF from definition:{indentD defn}\n\n\
          {err.toMessageData}"

end QPFTypes.QPFExpr
end
