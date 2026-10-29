module

public meta import Lean
public import QPFTypes.Theory.QPF.Cofix.WithBot
public import QPFTypes.Meta.QPFAttr.Cofix
public import QPFTypes.Meta.ProductiveBy.Intro
public import QPFTypes.Meta.CodefMono

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
2. translates the elaborated body into the possibly-partial type `PT = T.__partial`
   (see `Codef.Ctx.go`), and adds the result as `f.__partial : binders' → PT` via
   `partial_fixpoint`. In `binders'`, the parameters `xs` of a total type (`T`, or another
   instance of the same coinductive type, e.g. `Stream α` for `T = Stream β`) on which no
   other parameter depends become possibly-partial, i.e. `f.__partial` accepts partial
   values for them (see `withPartialParams`). It also proves that `f.__partial` is monotone in
   these (`f.__partial_mono`, see `QPFTypes.Meta.CodefMono`), so that `f` can be applied to
   possibly-partial values, e.g. to recursive calls of another function;
3. defines `f := fun binders => CofixWithBot.get (f.__partial (ofCofix xs)) h`, where
   `h : CofixWithBot.HasNoBot (f.__partial (ofCofix xs))` is proved by `tac`, after
   `productive_by_intro` has set up the coinduction (see also `with_motive` below), and
   proves `f.__partial_ofCofix : ofCofix (f xs) = f.__partial (ofCofix xs)`;
4. proves the unfolding equation `f.__unfold : ∀ binders, f binders = body`, where the
   recursive references in `body` are to `f` itself, by unfolding `f` and `f.__partial`
   once, splitting on `if`s and `match`es, and either rewriting with `CofixWithBot.get_mk`,
   or pushing `CofixWithBot.ofCofix` into `body`, or pulling it out of the translated body
   (see `addUnfoldEqns`). It is
   also added as `f.eq_1` and `f.eq_def`, so that `rw [f]`, `simp [f]` and `unfold f`
   use it, rather than unfolding to `CofixWithBot.get`.

## The translation

The translation is uniform: every occurrence of the type `T` becomes `PT` (and similarly for
the other instances of the same coinductive type),
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
    is what allows recursive calls, and possibly-partial parameters, to be destructed, as in
    `(f xs).tail`;
  - `codef` itself, for functions such as `Stream.map`: this allows these to be applied to
    recursive calls, as in `map g (f xs)`.

  Eliminators whose result is not of a coinductive type, such as `Stream.head`, have partial
  versions in continuation-passing style. An application `g as` of such an eliminator to a
  possibly-partial value, in a term `e[g as]` of type `T` (not under binders), is translated to
  `g.__partial as' (fun y => e'[y])`, see `Ctx.liftCPS?`. E.g., with `xs` possibly-partial,
  `cons (f xs.head) (map f xs.tail)` becomes
  `head.__partial xs (fun y => cons.__partial (f y) (map.__partial f (tail.__partial xs)))`.

  If there is no partial version, the translation fails. In particular, `Cofix.dest` cannot
  be applied to a possibly-partial value directly.

## Extending the motive with `with_motive`

The motive of `productive_by_intro` only contains the recursive calls `f.__partial ys`, which
does not suffice when the children of the translated body are not of this form, as for
```
codef cursedMap (f : α → β) (xs : Stream α) : Stream β :=
  cons (f xs.head) <| cons (f xs.head) (cursedMap f xs.tail).tail
with_motive
  cons ?x (cursedMap f ?xs).tail
productive_by
  tac
```
Each term `t` in `with_motive t₁, .., tₙ` is elaborated with the total type `T` as its
expected type, in the context of the parameters of `f`, and translated like the body. Its
metavariables, such as the named holes `?x`, are turned into existentials, which keep their
(total) types. This adds the disjunct `∃ ws, z = t'` to the motive, here
`∃ x xs, z = cons.__partial x (tail.__partial (cursedMap.__partial f (ofCofix xs)))`. Then
`productive_by_intro` produces one goal per disjunct, tagged `rec` and `with_motive_i`.

## Limitations

* Only `:=` bodies; no `where`, equation-style definitions, or `mutual`.
* Recursive calls must not be nested inside arguments of recursive calls.
* Partial versions of eliminators in continuation-passing style (e.g. `Stream.head`) are only
  used for applications outside of binders, in a term of type `T`.
* Parameters on which other parameters depend (e.g. `xs` in `(xs : Stream α) (h : P xs)`)
  are not made possibly-partial, and neither are the existentials of `with_motive`.
* `T`-typed inputs cannot be destructed inside the body (e.g. by `match`ing on
  `Cofix.dest xs`): the motive is translated as well, after which the pieces no longer
  fit back into recursive calls. Use non-recursive accessor functions instead.
* Recursive references are found syntactically, so local variables shadowing the
  function name, and generalized field notation (`xs.f`), are not supported.
-/

public meta section

namespace QPFTypes.Codef

open Lean Meta Elab Command Term

/-- `codef f binders : T := body (with_motive t,+)? productive_by tac`, see the module docstring. -/
syntax (name := codefCmd) declModifiers "codef " declId optDeclSig " := " term
  (" with_motive " term,+)?
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

/-- The data of a translation from `T = Cofix F α` to its possibly-partial analogue
`PT = T.__partial`, see `@[qpf]`. -/
structure Ctx where
  /-- The universe level, and the arguments `{n} (F) [QPF F] (α)` of `Cofix`. -/
  lvl : Level
  args : Array Expr
  /-- `T = Cofix F α`, as it appears in the declared type. -/
  T : Expr
  /-- `PT = c.__partial xs`, where `T = c xs` for a coinductive type `c` marked with `@[qpf]`. -/
  PT : Expr
  rawName : Name
  /-- The possibly-partial parameters of the function being translated (free variables of type
  `PT`), e.g. `xs` in `f.__partial (xs : PT)`. -/
  partials : Array Expr := #[]
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

/-- If `e` is a total type, its possibly-partial analogue. The total types are `T = c xs`
itself, up to reducible unfolding, and the other instances `c ys` of the same coinductive type
`c` (e.g. `Stream α`, besides `T = Stream β`), with possibly-partial analogue `c.__partial ys`.

Only reducible unfolding is used, so that types which merely compute to `T` (such as
`TypeVec.head (α ::: T)`) are kept, with `T` replaced inside of them: this keeps the
translated body in the shape the monotonicity lemmas expect. -/
def partialOf? (ctx : Ctx) (e : Expr) : MetaM (Option Expr) := do
  if e == ctx.T then return ctx.PT
  if e.hasLooseBVars then return none
  if let .const c _ := e.getAppFn then
    if ctx.T.getAppFn.isConstOf c then return ← QPFAttr.partialType? e
  if !(← isType e) then return none
  unless (← whnfR e).isAppOfArity ``QPF.Cofix 4 do return none
  if ← isDefEq e ctx.T then return ctx.PT
  return none

/-- Whether `e` is a total type, see `partialOf?`. -/
def isTotalType (ctx : Ctx) (e : Expr) : MetaM Bool :=
  return (← ctx.partialOf? e).isSome

/-- `ofCofix e`, for `e` of a total type (see `partialOf?`). -/
def mkOfCofix (ctx : Ctx) (e : Expr) : MetaM Expr := do
  if ← isDefEq (← inferType e) ctx.T then
    return mkApp (ctx.mkConst ``QPF.CofixWithBot.ofCofix) e
  mkAppM ``QPF.CofixWithBot.ofCofix #[e]

/-- Make `e` fit the `expected` type, inserting `ofCofix` when a total value is used
where a partial one is expected. -/
def coerce? (ctx : Ctx) (e expected : Expr) : MetaM (Option Expr) := do
  let ty ← inferType e
  if ← isDefEq ty expected then return some e
  if let some PT ← ctx.partialOf? ty then
    if ← isDefEq expected PT then return some (← ctx.mkOfCofix e)
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

/-- Whether `e` is possibly-partial after the translation, i.e. mentions a recursive call or a
possibly-partial parameter. This is a syntactic approximation, used to find the applications of
eliminators that need to be translated to their partial versions in continuation-passing style,
see `Ctx.liftCPS?`. -/
def isPartialSyn (ctx : Ctx) (e : Expr) : Bool :=
  mentionsConst e ctx.rawName || ctx.partials.any (e.containsFVar ·.fvarId!)

/-- Whether `g` has a partial version `g.__partial` in continuation-passing style (see
`QPFTypes.Meta.QPFElim`), i.e. one with an extra universe parameter, for its result type. -/
def isCPSElim (g : Name) (us : List Level) : MetaM Bool := do
  let some pInfo := (← getEnv).find? (g ++ partialSuffix) | return false
  return pInfo.levelParams.length == us.length + 1

/-- Find an application `g as` of an eliminator `g` whose partial version is in
continuation-passing style, to some possibly-partial argument (see `isPartialSyn`), in `e`, but
not under binders. The applications in the arguments of `g` are found first. -/
partial def findCPS? (ctx : Ctx) (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .mdata _ e => findCPS? ctx e
  | .app .. =>
    let fn := e.getAppFn
    for a in e.getAppArgs do
      if let some c ← findCPS? ctx a then return c
    if let .const g us := fn then
      if !e.hasLooseBVars && e.getAppArgs.any ctx.isPartialSyn then
        if ← isCPSElim g us then return e
    else if let some c ← findCPS? ctx fn then return c
    return none
  | _ => return none

mutual

/-- Translate `e`, see the module docstring. -/
partial def go (ctx : Ctx) (e : Expr) : MetaM Expr := do
  if let some PT ← ctx.partialOf? e then return PT
  -- Proofs (e.g. of preconditions passed to recursive calls) are about total values.
  if !e.hasLooseBVars && !mentionsConst e ctx.rawName && (← isProof e) then return e
  if let some e' ← ctx.liftCPS? e then return e'
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
  -- Recursive calls: the arguments are translated, and total ones passed where `f.__partial`
  -- expects a possibly-partial one are lifted with `ofCofix`.
  if fn.isConstOf ctx.rawName then
    if args.any (mentionsConst · ctx.rawName) then
      throwError "codef: nested recursive calls are not supported{indentExpr e}"
    let some e' ← ctx.fixArgs? ctx.recFn (← args.mapM (go ctx))
      | throwError "codef: cannot translate the recursive call{indentExpr e}"
    return e'
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
          for eliminators whose result is not of a coinductive type, are only used in a term of \
          a coinductive type, outside of binders (see `Ctx.liftCPS?`)"
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

/-- If `e` is of the total type `T`, and contains (not under binders) an application `g as` of
an eliminator `g` to a possibly-partial value, whose partial version is in continuation-passing
style (see `QPFTypes.Meta.QPFElim`), translate `e` to `g.__partial as' (fun y => e'[y])`. Here
`e'[y]` is the translation of `e`, with (every occurrence of) `g as` replaced by `y`. E.g.,
`cons (f xs.head) (map f xs.tail)` becomes
`head.__partial xs (fun y => cons.__partial (f y) (map.__partial f (tail.__partial xs)))`. -/
partial def liftCPS? (ctx : Ctx) (e : Expr) : MetaM (Option Expr) := do
  unless !e.hasLooseBVars && ctx.isPartialSyn e do return none
  let some PT ← ctx.partialOf? (← inferType e) | return none
  let some (lvl, PTArgs) ← QPFAttr.partialTypeArgs? PT | return none
  let some c ← findCPS? ctx e | return none
  let .const g us := c.getAppFn | return none
  let pName := g ++ partialSuffix
  let args' ← c.getAppArgs.mapM (go ctx)
  let some p ← ctx.fixArgs? (.const pName (us ++ [lvl])) args'
    | throwError "codef: cannot use `{.ofConstName pName}`, the partial version of \
        `{.ofConstName g}`, in{indentExpr c}\nit cannot be applied to the translated arguments\
        {indentD (MessageData.joinSep (args'.toList.map indentExpr) "")}"
  -- `{m G} [QPF G] {β}`, the universe and arguments of the result `PT = CofixWithBot G β`.
  let p := mkAppN p PTArgs
  let .forallE _ kTy _ _ ← whnf (← inferType p)
    | throwError "codef: unexpected type of{indentExpr p}"
  let .forallE _ R' _ _ ← whnf kTy
    | throwError "codef: unexpected type of the continuation of{indentExpr p}"
  let k ← withLocalDeclD (.mkSimple g.eraseMacroScopes.getString!) R' fun y => do
    let body ← go ctx (e.replace fun s => if s == c then some y else none)
    let some body ← ctx.coerce? body ctx.PT
      | throwError "codef: the translation{indentExpr body}
does not have type{indentExpr ctx.PT}"
    mkLambdaFVars #[y] body
  let lemma := g ++ partialOfCofixSuffix
  if (← getEnv).contains lemma then ctx.log.modify (·.push lemma)
  return mkApp p k

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
with `Cofix ?F ?α`. The partial type `PT` is `c.__partial xs`, where `T = c xs` for a
coinductive type `c` marked with `@[qpf]`. `cmd` is the command or attribute being elaborated,
for error messages. -/
def mkCtx (fullName rawName : Name) (T : Expr) (recFn : Expr := default)
    (log : Option (IO.Ref (Array Name)) := none) (cmd : MessageData := "codef") : MetaM Ctx := do
  let log ← match log with
    | some log => pure log
    | none => IO.mkRef #[]
  let lvl ← mkFreshLevelMVar
  let cofix := Expr.const ``QPF.Cofix [lvl]
  let (args, _, _) ← forallMetaTelescope (← inferType cofix)
  let pattern := mkAppN cofix args
  unless ← isDefEq T pattern do
    throwError "{cmd}: the type of `{fullName}` should be a `Cofix` type:\n\
      failed to unify{indentExpr T}\nwith{indentExpr pattern}"
  let some PT ← QPFAttr.partialType? T
    | throwError "{cmd}: the type{indentExpr T}\nhas no possibly-partial analogue \
        (`{partialSuffix}`); it should be a coinductive type marked with `@[qpf]`, e.g.,\
        {indentD "@[qpf] def Stream (α : Type) : Type := Cofix StreamF #t[α]"}"
  let lvl ← instantiateLevelMVars lvl
  let args ← args.mapM instantiateMVars
  return { lvl, args, T, PT, recFn, log, rawName }

/-- Introduce the parameters `xs` of a function `f` defined by `codef` again, as the parameters
of `f.__partial`, and call `k` on the new parameters. The parameters of type `T` on which no other
parameter depends become parameters of type `PT`, i.e. `f.__partial` accepts possibly-partial
values for them; the other parameters are kept. -/
def withPartialParams (ctx : Ctx) (xs : Array Expr) (k : Array Expr → MetaM α)
    (i : Nat := 0) (ys : Array Expr := #[]) : MetaM α := do
  if h : i < xs.size then
    let x := xs[i]
    let decl ← x.fvarId!.getDecl
    let dependedOn ← xs[i+1:].toArray.anyM fun y => return (← inferType y).containsFVar x.fvarId!
    let some PT ← ctx.partialOf? decl.type | return ← withPartialParams ctx xs k (i + 1) (ys.push x)
    if dependedOn then return ← withPartialParams ctx xs k (i + 1) (ys.push x)
    withLocalDecl decl.userName decl.binderInfo PT fun y =>
      withPartialParams ctx xs k (i + 1) (ys.push y)
  else
    k ys

/-- The arguments `xs` of `f`, as passed to `f.__partial`: those which `f.__partial` takes as
possibly-partial values (see `withPartialParams`) are lifted with `ofCofix`. -/
def partialArgs (ctx : Ctx) (xs : Array Expr) : MetaM (Array Expr) :=
  withPartialParams ctx xs fun xs' => (xs.zip xs').mapM fun (x, x') =>
    if x == x' then pure x else ctx.mkOfCofix x

/-- Prove and add `f.__partial_ofCofix : ofCofix (f xs) = f.__partial (ofCofix xs)`, for the
function `declName` defined by `codef`, where `raw` is its elaborated `f.__codef_raw`. This holds
by `CofixWithBot.ofCofix_get`, since `f xs := get (f.__partial (ofCofix xs)) _`. -/
def addCodefOfCofix (declName : Name) (raw : DefinitionVal) : TermElabM Unit := do
  let lvls := raw.levelParams.map mkLevelParam
  let (type, value) ← forallTelescope raw.type fun xs T => do
    let ctx ← mkCtx (privateToUserName declName) raw.name T
    let ofCofix := ctx.mkConst ``QPF.CofixWithBot.ofCofix
    let lhs := mkApp ofCofix (mkAppN (.const declName lvls) xs)
    let rhs := mkAppN (.const (declName ++ partialSuffix) lvls) (← partialArgs ctx xs)
    let goal ← mkEq lhs rhs
    let g ← mkFreshExprSyntheticOpaqueMVar goal
    let ofCofixGet := mkCIdent ``QPF.CofixWithBot.ofCofix_get
    let tac ← `(tactic| (delta $(mkCIdent declName):ident; exact $ofCofixGet:ident _ _))
    let gs ← try Tactic.run g.mvarId! (Tactic.evalTactic tac)
      catch ex => throwError "codef: failed to prove `{partialOfCofixSuffix}` for \
        `{privateToUserName declName}`:{indentD ex.toMessageData}"
    unless gs.isEmpty do
      throwError "codef: failed to prove `{partialOfCofixSuffix}` for \
        `{privateToUserName declName}`, unsolved goals:{goalsToMessageData gs}"
    return (← mkForallFVars xs goal, ← instantiateMVars (← mkLambdaFVars xs g))
  -- A `sorry` in the productivity proof has already been reported on `f`.
  withOptions (warn.sorry.set · false) <| addDecl <| .thmDecl {
    name := declName ++ partialOfCofixSuffix
    levelParams := raw.levelParams
    type, value
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

/-- The arguments of `simp only` pulling `ofCofix` out of a term, with the lemmas
`g.__partial_ofCofix` in `log` (see `Ctx.log`): right-to-left for those of the form
`ofCofix (g xs) = g.__partial (ofCofix xs)`, and left-to-right for those of the form
`g.__partial (ofCofix xs) k = k (g xs)`, of partial eliminators in continuation-passing style. -/
def mkOfCofixPull (log : Array Name) : MetaM (Array (TSyntax ``Parser.Tactic.simpLemma)) :=
  log.toList.eraseDups.toArray.filterMapM fun n => do
    let some info := (← getEnv).find? n | return none
    let pushes ← forallTelescope info.type fun _ eq => do
      let some (_, lhs, _) := eq.eq? | return false
      return lhs.isAppOf ``QPF.CofixWithBot.ofCofix
    if pushes then some <$> `(Parser.Tactic.simpLemma| ← $(mkCIdent n):ident)
    else some <$> `(Parser.Tactic.simpLemma| $(mkCIdent n):ident)

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
    let pull ← mkOfCofixPull (log.push (declName ++ partialOfCofixSuffix))
    let tac ← `(tactic| (repeat' split) <;> first
      | (erw [$(mkCIdent ``QPF.CofixWithBot.get_mk):ident]; rfl)
      | rfl
      | (refine $(mkCIdent ``QPF.CofixWithBot.get_eq_iff):ident.2 ?_
         try delta $(mkCIdent declName):ident
         repeat ($step:tactic)
         done)
      | (refine $(mkCIdent ``QPF.CofixWithBot.get_eq_iff):ident.2 ?_
         simp only [$pull,*]
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

/-- Elaborate and translate a `with_motive` term `stx` of the total type `T`, to the motive
disjunct `fun z => ∃ ys, z = stx'`. Here, `stx'` is the translation of `stx` (see `Ctx.go`),
whose recursive references are to `f.__partial` (`ctx.recFn`), and `ys` are the
metavariables of `stx`, such as the named holes `?x`. They keep their (total) types, like the
parameters of `f`. -/
def elabMotive (ctx : Ctx) (fullName : Name) (stx : Term) : TermElabM Expr := do
  -- Named holes `?x` refer to existing metavariables of the same name, e.g. from elaborating
  -- the body, or a previous `with_motive` term: forget these names.
  let userNames := (← getMCtx).userNames
  modifyMCtx ({ · with userNames := {} })
  let e ← elabTermEnsuringType (renameRecRefs fullName rawSuffix stx) ctx.T
  synthesizeSyntheticMVarsNoPostponing
  let r ← abstractMVars (← instantiateMVars e) (levels := false)
  modifyMCtx ({ · with userNames })
  lambdaBoundedTelescope r.expr r.mvars.size fun ys body => do
    let some body ← ctx.coerce? (← ctx.go body) ctx.PT
      | throwErrorAt stx "codef: the translated motive does not have type{indentExpr ctx.PT}"
    withLocalDeclD `z ctx.PT fun z => do
      let prop ← ys.foldrM (init := ← mkEq z body) fun y prop => do
        mkAppM ``Exists #[← mkLambdaFVars #[y] prop]
      mkLambdaFVars #[z] prop

@[command_elab codefCmd]
def elabCodef : CommandElab := fun stx => do
  let `($mods:declModifiers codef $declId:declId $sig:optDeclSig := $body
      $[with_motive $motives,*]?
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
  -- Steps B and C: check the result type, and translate the body. The parameters of type `T`
  -- become possibly-partial (see `withPartialParams`).
  let partialType ← forallTelescope raw.type fun xs T => do
    let ctx ← mkCtx fullName rawName T
    withPartialParams ctx xs fun xs' => mkForallFVars xs' ctx.PT
  let partialValue ← withLocalDeclD `rec partialType fun recFn => do
    let value ← forallTelescope raw.type fun xs T => do
      let ctx ← mkCtx fullName rawName T recFn log
      withPartialParams ctx xs fun xs' => do
        let ctx := { ctx with partials := xs'.filter (!xs.contains ·) }
        let body := (← instantiateLambda raw.value xs).replaceFVars xs xs'
        let some body ← ctx.coerce? (← ctx.go body) ctx.PT
          | throwError "codef: the translated body does not have type{indentExpr ctx.PT}"
        mkLambdaFVars xs' body
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
  -- `f.__partial_mono`, so that `f` can be used on possibly-partial values, see
  -- `QPFTypes.Meta.CodefMono`. This is best-effort: other uses of `f` do not need it.
  try
    if ← addCodefMono declName then
      Attribute.add (declName ++ partialMonoSuffix) `partial_fixpoint_monotone .missing
  catch ex =>
    trace[QPFTypes] "Not adding {declName ++ partialMonoSuffix}:{indentD ex.toMessageData}"
  -- Step E: the total version, given the productivity proof.
  let value ← forallTelescope raw.type fun xs T => do
    let ctx ← mkCtx fullName rawName T (.const partialName lvls)
    let p := mkAppN (.const partialName lvls) (← partialArgs ctx xs)
    let goal := mkApp (ctx.mkConst ``QPF.CofixWithBot.HasNoBot) p
    -- The `with_motive` disjuncts, passed on to `productive_by_intro`.
    let extras ← (motives.map (·.getElems) |>.getD #[]).mapM (elabMotive ctx fullName)
    let goal ← extras.foldrM (init := goal) fun extra goal =>
      mkAppM ``ProductiveByMotive #[extra, goal]
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
  -- `f.__partial_ofCofix : ofCofix (f xs) = f.__partial (ofCofix xs)`, so that other functions
  -- can use `f.__partial` in place of `f`, see `Ctx.goApp`.
  addCodefOfCofix declName raw
  -- Step F: the unfolding equation `f.__unfold : f xs = body`.
  addUnfoldEqns declName raw (← log.get)

end QPFTypes.Codef
