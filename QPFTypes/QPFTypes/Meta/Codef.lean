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
   `productive_by_intro` has set up the coinduction;
4. proves the unfolding equation `f.__unfold : ∀ binders, f binders = body`, where the
   recursive references in `body` are to `f` itself, by unfolding `f` and `f.__partial`
   once, splitting on `if`s and `match`es, and either rewriting with `CofixWithBot.get_mk`,
   or pushing `CofixWithBot.ofCofix` into `body` (see `addUnfoldEqns`). It is
   also added as `f.eq_1` and `f.eq_def`, so that `rw [f]`, `simp [f]` and `unfold f`
   use it, rather than unfolding to `CofixWithBot.get`.

## The translation

The translation is uniform: every occurrence of the type `T` becomes `PT`,
`Cofix.mk` (at `F`, `α`) becomes `CofixWithBot.mk`, and recursive calls go to
`f.__partial`. The `Cofix.mk` case is used to translate the bodies of `@[qpf_ctor]`
constructors; `codef` bodies are expected to use such constructors instead of `Cofix.mk`. Combinators that are polymorphic in their result type (`ite`, `dite`,
matchers, user-defined variations, ...) thus need no special treatment. The following
repairs are applied when an application becomes ill-typed:
* an argument of type `T` where `PT` is expected (e.g. an input `xs` or `xs.tail`) is
  wrapped in `CofixWithBot.ofCofix`;
* otherwise, the head constant `g` must have a partial version `g.__partial`, which is used
  instead. These are defined by attributes:
  - `@[qpf_ctor]`, for constructors such as `Stream.cons` (see `QPFTypes.Meta.QPFCtor`): this
    is what allows recursive calls to be guarded, as in `cons x (f xs)`;
  - `@[qpf_elim]`, for eliminators such as `Stream.tail` (see `QPFTypes.Meta.QPFElim`): this
    is what allows recursive calls to be destructed, as in `(f xs).tail`.

  If there is no partial version, the translation fails. In particular, `Cofix.dest` cannot
  be applied to a possibly-partial value directly.

## Limitations

* Only `:=` bodies; no `where`, equation-style definitions, or `mutual`.
* Recursive calls must not be nested inside arguments of recursive calls.
* Recursive calls can only be destructed by eliminators whose result is of a coinductive
  type (e.g. `Stream.tail`, but not `Stream.head`): partial versions in continuation-passing
  style are not used yet.
* `T`-typed inputs cannot be destructed inside the body (e.g. by `match`ing on
  `Cofix.dest xs`): the motive is translated as well, after which the pieces no longer
  fit back into recursive calls. Use non-recursive accessor functions instead.
* Recursive references are found syntactically, so local variables shadowing the
  function name, and generalized field notation (`xs.f`), are not supported.
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
/-- The suffix for the generated unfolding equation. -/
def unfoldSuffix : Name := `__unfold
/-- The suffix for the lemma `ofCofix (g xs) = g.__partial (ofCofix xs)` of a constructor or
eliminator `g`, see `QPFTypes.Meta.QPFCtor` and `QPFTypes.Meta.QPFElim`. -/
def partialOfCofixSuffix : Name := `__partial_ofCofix

/-- Reduce an application `(f ::: g) i x` (or `TypeVec.id i x`) of an arrow at a concrete
index `i`, to `f i' x` or `g x`. -/
def reduceArrowApp (e : Expr) : MetaM Expr :=
  whnfHeadPred e fun e => do
    let some n := e.getAppFn.constName? | return false
    return n ∈ [``TypeVec.appendFun, ``TypeVec.splitFun, ``TypeVec.id, ``Fin.cases,
      ``Fin.induction, ``Fin.induction.go, ``Eq.mpr, ``Eq.mp, ``cast, ``Eq.rec, ``Eq.ndrec] ||
      (← isMatcher n)

/--
`qpf_reduce_maps` reduces each `f <$$> x` in the goal whose `x` reduces to a constructor
application, mapping `f` over the fields: e.g. `(TypeVec.id ::: g) <$$> (a, b)` becomes
`(a, g b)` for a product functor. Fails if there is nothing to reduce.
-/
syntax (name := qpfReduceMaps) "qpf_reduce_maps" : tactic

@[tactic qpfReduceMaps]
def evalQpfReduceMaps : Tactic.Tactic := fun _ => Tactic.liftMetaTactic1 fun g => do
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    unless e.isAppOf ``MvFunctor.map do return .continue
    let e' ← whnfD e
    unless ← isConstructorApp e' do return .continue
    return .done (mkAppN e'.getAppFn (← e'.getAppArgs.mapM reduceArrowApp)))
  if t' == t then throwError "qpf_reduce_maps: no progress"
  g.change t'

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
  /-- Pairs `(x, y)` of a possibly-partial variable `x`, and a variable `y` standing for its
  root layer, which `Cofix.dest x` is translated to. Used by `@[qpf_elim]`, see
  `QPFTypes.Meta.QPFElim`. -/
  dests : Array (Expr × Expr) := #[]
  /-- Records the lemmas `g.__partial_ofCofix` of the constructors and eliminators `g` whose
  partial versions the translation used: these relate the translated body to the original
  one, see `addUnfoldEqns`. -/
  log : IO.Ref (Array Name)

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
  -- The constructor of `T`, in the body of a `@[qpf_ctor]` constructor.
  if fn.isConstOf ``QPF.Cofix.mk && args.size == 5 then
    if (← isDefEq args[1]! ctx.args[1]!) && (← isDefEq args[3]! ctx.args[3]!) then
      let mk := ctx.mkConst ``QPF.CofixWithBot.mk
      let x ← go ctx args[4]!
      let some x ← ctx.coerce? x (← inferType mk).bindingDomain!
        | throwError "codef: the argument of this constructor is not parametric in its \
            recursive positions{indentExpr e}"
      return mkApp mk x
  -- Destructors of the possibly-partial arguments of an `@[qpf_elim]` eliminator.
  if fn.isConstOf ``QPF.Cofix.dest && args.size == 5 then
    if let some (_, y) := ctx.dests.find? (·.1 == args[4]!) then
      return y
  let fn' ← if fn.isConst then pure fn else go ctx fn
  let args' ← args.mapM (go ctx)
  if let some e' ← ctx.fixArgs? fn' args' then
    return e'
  if let .const fnName us := fn then
    if fnName == ``QPF.Cofix.dest then
      throwError "codef: cannot destruct a possibly-partial value with `Cofix.dest`\
        {indentExpr e}\nuse an eliminator marked with `@[qpf_elim]` instead"
    -- The head has a partial version (a constructor marked with `@[qpf_ctor]`, or an
    -- eliminator marked with `@[qpf_elim]`): use it.
    let pName := fnName ++ partialSuffix
    if let some pInfo := (← getEnv).find? pName then
      let wrongType (msg : MessageData) : MetaM Expr :=
        throwError "codef: cannot use `{.ofConstName pName}`, the partial version of \
          `{.ofConstName fnName}`, in{indentExpr e}\n{msg}"
      unless pInfo.levelParams.length == us.length do
        return ← wrongType m!"it should have the same universe parameters as \
          `{.ofConstName fnName}`. Note that partial versions in continuation-passing style, \
          for eliminators whose result is not of a coinductive type, are not supported yet"
      let p := Expr.const pName us
      let some e' ← ctx.fixArgs? p args'
        | return ← wrongType m!"it cannot be applied to the translated arguments{indentD
            (MessageData.joinSep (args'.toList.map indentExpr) "")}"
      let expected ← go ctx (← inferType e)
      let actual ← inferType e'
      unless ← isDefEq actual expected do
        return ← wrongType m!"the result has type{indentExpr actual}\nbut is expected to have \
          type{indentExpr expected}"
      let lemma := fnName ++ partialOfCofixSuffix
      if (← getEnv).contains lemma then ctx.log.modify (·.push lemma)
      return e'
    throwError "codef: cannot translate{indentExpr e}\n`{.ofConstName fnName}` is applied to \
      a possibly-partial value, but has no partial version (`{partialSuffix}`); mark it with \
      `@[qpf_ctor]` if it is a constructor, or with `@[qpf_elim]` if it is an eliminator"
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
def mkCtx (fullName rawName : Name) (T : Expr) (recFn : Expr := default)
    (log : Option (IO.Ref (Array Name)) := none) : MetaM Ctx := do
  let log ← match log with
    | some log => pure log
    | none => IO.mkRef #[]
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
    lvl, args, T, recFn, log
    PT := mkAppN (.const ``QPF.CofixWithBot [lvl]) args
    rawName
  }

/-- One step of pushing `ofCofix` into a term, with the lemmas `g.__partial_ofCofix` in `log`
(see `Ctx.log`), `CofixWithBot.ofCofix_mk` and `CofixWithBot.ofCofix_get`, or by reducing the
maps that the latter introduce (`qpf_reduce_maps`). -/
def mkOfCofixStep (log : Array Name) : MetaM (TSyntax `tactic) := do
  -- The terms involved are only type-correct up to unfolding (e.g. of
  -- `TypeVec.head (α ::: T)`), hence `erw`. Since `erw` matches up to unfolding, the generic
  -- lemmas come last: e.g. `ofCofix_get` would otherwise match `ofCofix (Stream.tail (get x h))`,
  -- by unfolding `Stream.tail`.
  let lemmas := log.toList.eraseDups.toArray ++
    #[``QPF.CofixWithBot.ofCofix_mk, ``QPF.CofixWithBot.ofCofix_get]
  lemmas.foldrM (init := ← `(tactic| qpf_reduce_maps)) fun n tac =>
    `(tactic| first | erw [$(mkCIdent n):ident] | ($tac:tactic))

/-- Prove and add the unfolding equation `f.__unfold : ∀ xs, f xs = body` for the function
`declName` defined by `codef`, where `raw` is its elaborated `f.__codef_raw`, and `body` is the
latter's body with recursive calls to `f` itself. The equation is also registered as `f.eq_1`
and `f.eq_def`, to be used by `rw [f]`, `simp [f]` and `unfold f`.

The equation is first attempted by unfolding `CofixWithBot.get` on the outer constructor, which
suffices when the children of the translated body are recursive calls. Otherwise (e.g. with
nested constructors, or partial eliminators of recursive calls), it is reduced, with
`CofixWithBot.get_eq_iff`, to `body' = ofCofix body`, where `body'` is the translated body, and
`ofCofix` is pushed into `body` with `erw`, using the lemmas in `log` (see `Ctx.log`). -/
def addUnfoldEqns (declName : Name) (raw : DefinitionVal) (log : Array Name) :
    TermElabM Unit := do
  let fullName := privateToUserName declName
  let lvls := raw.levelParams.map mkLevelParam
  let (type, value) ← forallTelescope raw.type fun xs _ => do
    let body := (← instantiateLambda raw.value xs).replace fun e =>
      if e.isConstOf raw.name then some (.const declName lvls) else none
    let lhs := mkAppN (.const declName lvls) xs
    let eq ← mkEq lhs body
    -- `f xs` unfolds to `CofixWithBot.get (f.__partial xs) _`; unfold `f.__partial` once.
    let some lhs' ← unfoldDefinition? lhs
      | throwError "codef: failed to unfold `{fullName}`"
    let r ← unfold lhs' (declName ++ partialSuffix)
    let g ← mkFreshExprSyntheticOpaqueMVar (← mkEq r.expr body)
    let step ← mkOfCofixStep log
    let tac ← `(tactic| (repeat' split) <;> first
      | (erw [$(mkCIdent ``QPF.CofixWithBot.get_mk):ident]; rfl)
      | rfl
      | (refine $(mkCIdent ``QPF.CofixWithBot.get_eq_iff):ident.2 ?_
         try delta $(mkCIdent declName):ident
         repeat ($step:tactic)
         done))
    let gs ← try Tactic.run g.mvarId! (Tactic.evalTactic tac)
      catch ex => throwError "codef: failed to prove `{unfoldSuffix}` for `{fullName}`:\
        {indentD ex.toMessageData}"
    unless gs.isEmpty do
      throwError "codef: failed to prove `{unfoldSuffix}` for `{fullName}`, \
        unsolved goals:{goalsToMessageData gs}"
    let value ← instantiateMVars (← mkEqTrans (← r.getProof) g)
    return (← mkForallFVars xs eq, ← mkLambdaFVars xs value)
  let unfoldName := declName ++ unfoldSuffix
  -- A `sorry` in the productivity proof has already been reported on `f`.
  withOptions (warn.sorry.set · false) <| addDecl <| .thmDecl {
    name := unfoldName
    levelParams := raw.levelParams
    type, value
  }
  -- Register it as the equation lemmas of `f`, used by `rw [f]`, `simp [f]` (`f.eq_1`) and
  -- `unfold f` (`f.eq_def`): these are generated on demand, unless they already exist.
  -- Marking `f` as recursive keeps `simp [f]` from also delta-unfolding `f`.
  markAsRecursive declName
  for suffix in [eqn1ThmSuffix, unfoldThmSuffix] do
    addDecl <| .thmDecl {
      name := mkEqLikeNameFor (← getEnv) declName suffix
      levelParams := raw.levelParams
      type, value := .const unfoldName lvls
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
  let log ← IO.mkRef #[]
  let lvls := raw.levelParams.map mkLevelParam
  let docCtx := (← getLCtx, ← getLocalInstances)
  -- Steps B and C: check the result type, and translate the body.
  let partialType ← forallTelescope raw.type fun xs T => do
    mkForallFVars xs (← mkCtx fullName rawName T).PT
  let partialValue ← withLocalDeclD `rec partialType fun recFn => do
    let value ← forallTelescope raw.type fun xs T => do
      let ctx ← mkCtx fullName rawName T recFn log
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
  -- Step F: the unfolding equation `f.__unfold : f xs = body`.
  addUnfoldEqns declName raw (← log.get)

end QPFTypes.Codef
