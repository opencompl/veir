module

public meta import Lean

public import QPFTypes.Meta.QPFExpr.Basic
public meta import QPFTypes.Meta.Options

public meta import QPFTypes.Meta.Basic

/-!
# The composition pipeline

This file implements `QPFExpr.ofTypeExprAux`, which builds a QPFExpr given a Lean
expression, of type `Type u`, and an array of (live) free variables.
This implements what is called the "composition pipeline" in [1].

## References

[1] Alex Keizer. Implementing a definitional (co)datatype package in Lean 4,
based on quotients of polynomial functors.
https://eprints.illc.uva.nl/id/eprint/2239/1/MoL-2023-03.text.pdf

-/

meta section

namespace QPFTypes
open Lean Elab Meta

namespace QPFExpr

/--
Given a target expression `$G $a₁ ⋯ $aₘ`, find the largest head `$G $a₁ ⋯ $aⱼ`
such that
* the head does not mention any of the live variables, and
* the head is a `k`-ary QPF in curried form, i.e., an instance of
  `QPF (TypeFun.ofCurried $head)` can be synthesized, where `k = m - j`.

Returns that head, as a `QPFExpr`, together with the `k` remaining arguments.
-/
private def parseApp (u : Level) (isLiveVar : FVarId → Bool) (target : Expr) :
    MetaM ((k : Nat) × QPFExpr u k × Vector Expr k) := do
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
    return ⟨k, { typefun, qpf }, rest.toVector⟩

  if let some err := liveVarError? then
    throwError err
  else
    throwError "\
      failed to find a QPF in the head of the application:{indentExpr target}\n\
      note that the head, after applying it to zero or more of the arguments, \
      must be a type function with a `QPF` instance"

/-- Implementation of `ofTypeExpr` -/
partial def ofTypeExprCore (u : Level) (liveVars : Vector FVarId n) (target : Expr) :
    MetaM (QPFExpr u n) :=
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
  ofApp (target : Expr) : MetaM (QPFExpr u n) := do
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
  ofForall (A body : Expr) : MetaM (QPFExpr u n) := do
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
  ofSigma (A family : Expr) : MetaM (QPFExpr u n) := do
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
private def assertCurriedDefEq (q : QPFExpr u n)
    (liveVars : Vector FVarId n) (target : Expr) : MetaM Unit := do
  let curried := mkApp2 (mkConst ``TypeFun.curry [u]) (toExpr n) q.typefun
  let expected ← mkLambdaFVars (liveVars.toArray.map Expr.fvar) target
  unless ← withoutModifyingState (isDefEq curried expected) do
    throwError "\
      debug assertion failed, the derived type function{indentExpr curried}\n\
      is not definitionally equal to{indentExpr expected}"

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

For example, `ofTypeExpr #v['α, 'β] ${ α → β }` (using pseudo quotation syntax)
throws an error, since `α` is listed as a live variable and is used on the left
side of an arrow, but `ofTypeExpr #v['β] ${ α → β }` is accepted.

Note that arity of the resulting QPF is the number of live variables.
That is, the resulting QPF is the uncurried version of the type function
`fun $liveVars... => $target`, which abstracts over the given live variables.
Converting the type function of the returned QPFExpr into a curried function,
by applying `TypeFun.curry` to it, yields an expression which is
definitionally equal to this abstracted expression.
-/
public def ofTypeExpr (liveVars : Vector FVarId n) (target : Expr) :
    MetaM (Σ u, QPFExpr u n) :=
  try
    let u ← getDecLevel target
    for v in liveVars do
      let actual ← v.getType
      let expected := .sort u.succ
      unless ← isDefEq actual expected do
        throwError "Live variable {v} {← mkHasTypeButIsExpectedMsg actual expected}"

    let qpf ← ofTypeExprCore u liveVars target
    if ← getBoolOption `QPFTypes.debug false then
      qpf.assertCurriedDefEq liveVars target
    return ⟨_, qpf⟩
  catch err =>
    let liveVars := toMessageData liveVars.toList
    throwError "\
      While deriving a QPF from type expression:{indentExpr target}\n\
      With live free variables:{indentD liveVars}\n\n\
      {err.toMessageData}
      "

end QPFTypes.QPFExpr
end
