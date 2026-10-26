module

public meta import Lean
public import QPFTypes.Theory.QPF.Cofix.WithBot
public import QPFTypes.Meta.ProductiveBy.Intro

/-!
# The `codef` command (proof of concept)

```
codef f binders : T := body
productive_by tac
```
defines a corecursive function into a coinductive type `T = Cofix F α`, without a
syntactic productivity check. Instead, it

1. elaborates `body` like `def` would, with `T` as the expected type, by running the
   stock `def` elaborator on `unsafe def f.__codef_raw binders : T := body`, where
   recursive references to `f` are renamed to `f.__codef_raw`;
2. translates the elaborated body into the possibly-partial type `PT = CofixWithBot F α`
   (see `Codef.Ctx.go`), and adds the result as `f.__partial : binders → PT` via
   `partial_fixpoint`;
3. defines `f := fun binders => CofixWithBot.get (f.__partial binders) h`, where
   `h : CofixWithBot.HasNoBot (f.__partial binders)` is proved by `tac`, after
   `productive_by_intro` has set up the coinduction.

## The translation

The translation is uniform: every occurrence of the type `T` becomes `PT`,
`Cofix.mk` (at `F`, `α`) becomes `CofixWithBot.mk`, and recursive calls go to
`f.__partial`. Combinators that are polymorphic in their result type (`ite`, `dite`,
matchers, user-defined variations, ...) thus need no special treatment. Two repairs are
applied when an application becomes ill-typed:
* an argument of type `T` where `PT` is expected (e.g. an input `xs` or `xs.tail`) is
  wrapped in `CofixWithBot.ofCofix`;
* otherwise, the head constant is unfolded (e.g. a user-defined `Stream.cons`), and the
  result is translated instead.

## Limitations

* Only `:=` bodies; no `where`, equation-style definitions, or `mutual`.
* Recursive calls must not be nested inside arguments of recursive calls.
* `T`-typed inputs cannot be destructed inside the body (e.g. by `match`ing on
  `Cofix.dest xs`): the motive is translated as well, after which the pieces no longer
  fit back into recursive calls. Use non-recursive accessor functions instead.
* Recursive references are found syntactically, so local variables shadowing the
  function name, and generalized field notation (`xs.f`), are not supported.
* Monotonicity of the constructors is left to `@[partial_fixpoint_monotone]` lemmas
  about `CofixWithBot.mk`, see `CofixWithBot.mk_map_mono`.
-/

public meta section

namespace QPFTypes.Codef

open Lean Meta Elab Command Term

/-- `codef f binders : T := body productive_by tac`, see the module docstring. -/
syntax (name := codefCmd) declModifiers "codef " declId optDeclSig " := " term
  " productive_by " Lean.Parser.Tactic.tacticSeq : command

/-- The suffix for the elaborated, but untranslated, unsafe definition. -/
def rawSuffix : Name := `__codef_raw
/-- The suffix for the translated, possibly-partial definition. -/
def partialSuffix : Name := `__partial

/-- The data of a translation from `T = Cofix F α` to `PT = CofixWithBot F α`. -/
structure Ctx where
  /-- The universe level, and the arguments `{n} (F) [QPF F] (α)` of `Cofix`. -/
  lvl : Level
  args : Array Expr
  /-- `T = Cofix F α`, as it appears in the declared type. -/
  T : Expr
  /-- `PT = CofixWithBot F α`. -/
  PT : Expr
  rawName : Name
  /-- Stands for `f.__partial` during the translation (a free variable). -/
  recFn : Expr

/-- Whether `e` mentions the constant `c`. -/
def mentionsConst (e : Expr) (c : Name) : Bool :=
  (e.find? (·.isConstOf c)).isSome

namespace Ctx

/-- `@c.{lvl} n F inst α`. -/
def mkConst (ctx : Ctx) (c : Name) : Expr :=
  mkAppN (.const c [ctx.lvl]) ctx.args

/-- Whether `e` is the total type `T`, up to reducible unfolding.

Only reducible unfolding is used, so that types which merely compute to `T` (such as
`TypeVec.head (α ::: T)`) are kept, with `T` replaced inside of them: this keeps the
translated body in the shape the monotonicity lemmas expect. -/
def isTotalType (ctx : Ctx) (e : Expr) : MetaM Bool := do
  if e == ctx.T then return true
  if e.hasLooseBVars || !(← isType e) then return false
  unless (← whnfR e).isAppOfArity ``QPF.Cofix 4 do return false
  isDefEq e ctx.T

/-- Make `e` fit the `expected` type, inserting `ofCofix` when a total value is used
where a partial one is expected. -/
def coerce? (ctx : Ctx) (e expected : Expr) : MetaM (Option Expr) := do
  let ty ← inferType e
  if ← isDefEq ty expected then return some e
  if (← isDefEq expected ctx.PT) && (← isDefEq ty ctx.T) then
    return some (mkApp (ctx.mkConst ``QPF.CofixWithBot.ofCofix) e)
  return none

/-- Re-check the (translated) arguments of an application against the (translated) function
type, applying `coerce?` where needed. Returns `none` if the application is ill-typed. -/
def fixArgs? (ctx : Ctx) (fn : Expr) (args : Array Expr) : MetaM (Option Expr) := do
  let mut fnTy ← inferType fn
  let mut args := args
  for i in [:args.size] do
    let .forallE _ d b _ ← whnf fnTy | return none
    let some a ← ctx.coerce? args[i]! d | return none
    args := args.set! i a
    fnTy := b.instantiate1 a
  return mkAppN fn args

mutual

/-- Translate `e`, see the module docstring. -/
partial def go (ctx : Ctx) (e : Expr) : MetaM Expr := do
  if ← ctx.isTotalType e then return ctx.PT
  -- Proofs (e.g. of preconditions passed to recursive calls) are about total values.
  if !e.hasLooseBVars && !mentionsConst e ctx.rawName && (← isProof e) then return e
  match e with
  | .const n _ =>
    if n == ctx.rawName then return ctx.recFn else return e
  | .app .. => goApp ctx e
  | .lam n d b bi =>
    withLocalDecl n bi (← go ctx d) fun x => do
      mkLambdaFVars #[x] (← go ctx (b.instantiate1 x))
  | .forallE n d b bi =>
    withLocalDecl n bi (← go ctx d) fun x => do
      mkForallFVars #[x] (← go ctx (b.instantiate1 x))
  | .letE n t v b nondep =>
    let t' ← go ctx t
    let some v' ← ctx.coerce? (← go ctx v) t'
      | throwError "codef: cannot translate the value of `{n}`{indentExpr v}"
    withLetDecl n t' v' (nondep := nondep) fun x => do
      mkLetFVars #[x] (← go ctx (b.instantiate1 x)) (generalizeNondepLet := false)
  | .mdata d e' => return .mdata d (← go ctx e')
  | .proj s i e' => return .proj s i (← go ctx e')
  | _ => return e

/-- Translate an application, see the module docstring. -/
partial def goApp (ctx : Ctx) (e : Expr) : MetaM Expr := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  -- Recursive calls: the arguments keep their (total) types.
  if fn.isConstOf ctx.rawName then
    if args.any (mentionsConst · ctx.rawName) then
      throwError "codef: nested recursive calls are not supported{indentExpr e}"
    return mkAppN ctx.recFn args
  -- Constructors of `T`.
  if fn.isConstOf ``QPF.Cofix.mk && args.size == 5 then
    if (← isDefEq args[1]! ctx.args[1]!) && (← isDefEq args[3]! ctx.args[3]!) then
      let mk := ctx.mkConst ``QPF.CofixWithBot.mk
      let x ← go ctx args[4]!
      let some x ← ctx.coerce? x (← inferType mk).bindingDomain!
        | throwError "codef: the argument of this constructor is not parametric in its \
            recursive positions{indentExpr e}"
      return mkApp mk x
  let fn' ← if fn.isConst then pure fn else go ctx fn
  let args' ← args.mapM (go ctx)
  if let some e' ← ctx.fixArgs? fn' args' then
    return e'
  -- The head is not polymorphic in `T`: unfold it, and try again.
  if fn.isConst then
    if let some e' ← unfoldDefinition? e then
      return ← go ctx e'.headBeta
  throwError "codef: cannot translate{indentExpr e}"

end

end Ctx

/-- Rename references to the function being defined (`fullName`) in `body` by appending
`suffix`. A reference is any identifier whose components are a suffix of `fullName`. -/
def renameRecRefs (fullName suffix : Name) (body : Syntax) : Syntax :=
  Id.run <| body.replaceM fun stx => pure <|
    if stx.isIdent then
      let n := stx.getId.eraseMacroScopes
      let cs := n.components
      let fcs := fullName.components
      if !n.isAnonymous && cs.length ≤ fcs.length && fcs.drop (fcs.length - cs.length) == cs then
        some (mkIdentFrom stx (n ++ suffix))
      else none
    else none

/-- The termination hints for a `partial_fixpoint` definition. -/
def partialFixpointHints (ref : Syntax) : TerminationHints :=
  { TerminationHints.none with ref, partialFixpoint? := some { ref, term? := none } }

/-- The translation context for a function `fullName` with codomain `T`, which is unified
with `Cofix ?F ?α`. -/
def mkCtx (fullName rawName : Name) (T : Expr) (recFn : Expr := default) : MetaM Ctx := do
  let lvl ← mkFreshLevelMVar
  let cofix := Expr.const ``QPF.Cofix [lvl]
  let (args, _, _) ← forallMetaTelescope (← inferType cofix)
  let pattern := mkAppN cofix args
  unless ← isDefEq T pattern do
    throwError "codef: the type of `{fullName}` should be a `Cofix` type:\n\
      failed to unify{indentExpr T}\nwith{indentExpr pattern}"
  let lvl ← instantiateLevelMVars lvl
  let args ← args.mapM instantiateMVars
  return {
    lvl, args, T, recFn
    PT := mkAppN (.const ``QPF.CofixWithBot [lvl]) args
    rawName
  }

@[command_elab codefCmd]
def elabCodef : CommandElab := fun stx => do
  let `($mods:declModifiers codef $declId:declId $sig:optDeclSig := $body
      productive_by $tac) := stx | throwUnsupportedSyntax
  let userName := declId.raw[0].getId
  -- The kernel name, as `def` would choose it (e.g. private, in a module).
  let (modifiers, declName) ← liftTermElabM do
    let modifiers ← elabModifiers mods
    let r ← Term.expandDeclId (← getCurrNamespace) (← getLevelNames) declId modifiers
    return (modifiers, r.declName)
  let fullName := privateToUserName declName
  let partialName := declName ++ partialSuffix
  -- Step A: elaborate as an `unsafe def`, so that neither termination checking nor
  -- `Inhabited` are needed.
  let rawUserName := userName ++ rawSuffix
  let rawDeclId : TSyntax ``Parser.Command.declId :=
    ⟨declId.raw.setArg 0 (mkIdentFrom declId.raw[0] rawUserName)⟩
  let rawBody : Term := ⟨renameRecRefs fullName rawSuffix body⟩
  elabCommand <| ← `(unsafe def $rawDeclId $sig:optDeclSig := $rawBody)
  let rawName ← try liftCoreM <| resolveGlobalConstNoOverload (mkIdent rawUserName)
    catch _ => throwError "codef: failed to elaborate `{fullName}`"
  let some (.defnInfo raw) := (← getEnv).find? rawName
    | throwError "codef: failed to elaborate `{fullName}`"
  liftTermElabM do
  let lvls := raw.levelParams.map mkLevelParam
  let docCtx := (← getLCtx, ← getLocalInstances)
  -- Steps B and C: check the result type, and translate the body.
  let partialType ← forallTelescope raw.type fun xs T => do
    mkForallFVars xs (← mkCtx fullName rawName T).PT
  let partialValue ← withLocalDeclD `rec partialType fun recFn => do
    let value ← forallTelescope raw.type fun xs T => do
      let ctx ← mkCtx fullName rawName T recFn
      let body ← instantiateLambda raw.value xs
      let some body ← ctx.coerce? (← ctx.go body) ctx.PT
        | throwError "codef: the translated body does not have type{indentExpr ctx.PT}"
      mkLambdaFVars xs body
    return (value.abstract #[recFn]).instantiate1 (.const partialName lvls)
  -- Step D: the possibly-partial version, via `partial_fixpoint`.
  addPreDefinitions docCtx #[{
    ref := stx
    kind := .def
    levelParams := raw.levelParams
    modifiers := {}
    declName := partialName
    binders := mkNullNode
    type := partialType
    value := partialValue
    termination := partialFixpointHints stx
  }]
  -- Step E: the total version, given the productivity proof.
  let value ← forallTelescope raw.type fun xs T => do
    let ctx ← mkCtx fullName rawName T
    let p := mkAppN (.const partialName lvls) xs
    let goal := mkApp (ctx.mkConst ``QPF.CofixWithBot.HasNoBot) p
    let h ← elabTermEnsuringType (← `(by productive_by_intro; ($tac:tacticSeq))) goal
    synthesizeSyntheticMVarsNoPostponing
    let h ← instantiateMVars h
    let get := ctx.mkConst ``QPF.CofixWithBot.get
    let .forallE _ instTy _ _ ← whnf (← inferType get)
      | throwError "codef: unexpected type of `CofixWithBot.get`"
    let inst ← synthInstance instTy
    mkLambdaFVars xs (mkApp3 get inst p h)
  addPreDefinitions docCtx #[{
    ref := stx
    kind := .def
    levelParams := raw.levelParams
    modifiers := { modifiers with isUnsafe := false }
    declName
    binders := mkNullNode
    type := raw.type
    value
    termination := { TerminationHints.none with ref := stx }
  }]

end QPFTypes.Codef
