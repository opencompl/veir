module

public meta import Lean
public import QPFTypes.Meta.QPFElim

/-!
# The `@[qpf_ctor]` attribute

`codef` translates a corecursive body from a total coinductive type `T = Cofix F α` into the
possibly-partial `PT = CofixWithBot F α` (see `QPFTypes.Meta.Codef`). The results of recursive
calls are then possibly-partial, and cannot be passed to the constructors of `T`, such as
`Stream.cons x (f xs)`.

Marking such a constructor `g` with `@[qpf_ctor]` defines its partial version `g.__partial`,
which `codef` uses in place of `g` whenever `g` is applied to a possibly-partial value. Every
argument of `g` of type `T` becomes an argument of type `PT`, and the body of `g` is translated
like the body of a `codef`: in particular, `Cofix.mk` becomes `CofixWithBot.mk`. For example,
```
@[qpf_ctor] def Stream.cons (x : α) (xs : Stream α) : Stream α := Cofix.mk (x, xs)
```
defines
```
Stream.cons.__partial (x : α) (xs : PStream α) : PStream α := CofixWithBot.mk (x, xs)
```

As with `@[qpf_elim]`, the attribute also proves the monotonicity lemma `g.__partial_mono`,
and registers it with `@[partial_fixpoint_monotone]`, so that `partial_fixpoint` accepts
recursive calls under `g`. It also proves
`g.__partial_ofCofix : ofCofix (g xs) = g.__partial (ofCofix xs)`, which `codef` uses to prove
unfolding equations. Finally, if `g.__partial xs` unfolds to a single layer `CofixWithBot.mk L`,
it proves `g.__dest_partial : Cofix.dest (g.__partial xs) = Comp.mk (some L)` and
`g.__get_dest_partial : Comp.get (Cofix.dest (g.__partial xs)) = some L`, marked with
`@[simp, qpf_productive_by, grind =]` (the latter as a `simp` pre-lemma, `↓`), for productivity
proofs: in particular, `productive_by_intro` already rewrites with them.

## Limitations

* The result of `g` must be of a `Cofix` type `T`, and only the arguments of type `T` become
  possibly-partial.
* Arguments whose types depend on an argument of type `T` are not supported.
* The monotonicity proof (`qpf_mk_mono`) only finds the children of a `CofixWithBot.mk` layer
  through applications, not under binders, and relies on the map of `F` reducing
  definitionally, as it does for functors such as products and sums.
-/

public meta section

namespace QPFTypes.Codef

open Lean Meta Elab

/-- Replace the children of a layer `L`, i.e. its maximal subterms of type `PT` which can be
reached through applications, by fresh (undeclared) free variables. Records the pairs of
these variables and the children they replace. -/
partial def abstractChildren (PT L : Expr) : StateRefT (Array (FVarId × Expr)) MetaM Expr := do
  if !L.hasLooseBVars then
    if ← isDefEq (← inferType L) PT then
      let fvarId ← mkFreshFVarId
      modify (·.push (fvarId, L))
      return .fvar fvarId
  match L with
  | .app f a => return .app (← abstractChildren PT f) (← abstractChildren PT a)
  | .mdata d e => return .mdata d (← abstractChildren PT e)
  | _ => return L

/-- The numeral `j : Fin k`, for `j < k`. -/
def mkFinLit (k j : Nat) : Expr :=
  let r := mkRawNatLit j
  mkApp3 (.const ``OfNat.ofNat [0]) (mkApp (.const ``Fin []) (mkNatLit k)) r
    (mkApp3 (.const ``Fin.instOfNat []) (mkNatLit k)
      (mkApp (.const ``Nat.instNeZeroSucc []) (mkNatLit (k - 1))) r)

/--
`qpf_mk_mono` reduces a goal `monotone (fun z => CofixWithBot.mk L[z])` to the monotonicity of
the children `fun z => vⱼ[z]` of the layer `L[z]`, i.e. its maximal subterms of the type
`CofixWithBot F α`. It applies `CofixWithBot.mk_map_mono` with `ι := Fin k`, where `k` is the
number of children: the fixed layer `s` is `L` with the children replaced by their indices, and
the children are `fun z => Fin.cases v₀[z] (Fin.cases v₁[z] ...)`.
-/
syntax (name := qpfMkMono) "qpf_mk_mono" : tactic

@[tactic qpfMkMono]
def evalQpfMkMono : Tactic.Tactic := fun _ => Tactic.liftMetaTactic fun g => g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let err {α} (msg : MessageData) : MetaM α :=
    throwError "qpf_mk_mono: {msg}{indentExpr tgt}"
  unless tgt.isAppOfArity ``Lean.Order.monotone 5 do
    err m!"expected a goal of the form `monotone (fun z => CofixWithBot.mk _)`, got"
  let #[γ, _, _, _, fn] := tgt.getAppArgs | unreachable!
  let .lam zn zty b zbi := fn
    | err m!"expected a goal of the form `monotone (fun z => CofixWithBot.mk _)`, got"
  -- Compute, under `z`: the universe level and arguments of `CofixWithBot`, the fixed layer
  -- `s : F (α ::: Fin k)`, and the children `fun z => vⱼ[z]`.
  let (lvl, args, k, s, vs) ← withLocalDecl zn zbi zty fun z => do
    let body := b.instantiate1 z
    unless body.isAppOfArity ``QPF.CofixWithBot.mk 5 do
      err m!"expected a goal of the form `monotone (fun z => CofixWithBot.mk _)`, got"
    let lvl := body.getAppFn.constLevels!.head!
    let args := body.getAppArgs[:4].toArray
    let PT := mkAppN (.const ``QPF.CofixWithBot [lvl]) args
    let (L, children) ← (abstractChildren PT body.appArg!).run #[]
    let k := children.size
    let ι := mkApp (.const ``Fin []) (mkNatLit k)
    let s := (L.replace fun e => if e == PT then some ι else none).replaceFVars
      (children.map (.fvar ·.1)) (Array.ofFn fun (j : Fin k) => mkFinLit k j)
    if s.containsFVar z.fvarId! then
      err m!"the layer depends on `{zn}` other than through its children of \
        type{indentExpr PT}\nin"
    let vs ← children.mapM fun (_, v) => mkLambdaFVars #[z] v
    return (lvl, args, k, s, vs)
  let PT := mkAppN (.const ``QPF.CofixWithBot [lvl]) args
  let ι := mkApp (.const ``Fin []) (mkNatLit k)
  -- The children `f := fun z => Fin.cases v₀[z] (... Fin.elim0)`, and the proof of its
  -- monotonicity, with a new goal for the monotonicity of each child.
  let goals ← vs.mapM fun v => do
    mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Lean.Order.monotone #[v])
  let (f, hf) ← withLocalDecl zn zbi zty fun z => do
    let elim0 := mkApp (.const ``Fin.elim0 [lvl.succ]) PT
    let mut f ← mkLambdaFVars #[z] elim0
    let mut hf ← mkAppOptM ``Lean.Order.monotone_const #[γ, none, none, none, elim0]
    for j in (List.range k).reverse do
      let motive ← withLocalDeclD `i (mkApp (.const ``Fin []) (mkNatLit (k - j))) fun i =>
        mkLambdaFVars #[i] PT
      let cases := mkApp4 (.const ``Fin.cases [lvl.succ]) (mkNatLit (k - j - 1)) motive
        (vs[j]!.beta #[z]) (f.beta #[z])
      hf ← mkAppOptM ``QPF.CofixWithBot.monotone_finCases
        #[γ, none, PT, none, mkNatLit (k - j - 1), vs[j]!, f, goals[j]!, hf]
      f ← mkLambdaFVars #[z] cases
    return (f, hf)
  let lemma ← try
      mkAppOptM ``QPF.CofixWithBot.mk_map_mono
        #[args[0]!, args[1]!, args[2]!, args[3]!, γ, none, none, ι, s, f, hf]
    catch ex => err m!"failed to apply `CofixWithBot.mk_map_mono`:{indentD ex.toMessageData}\n\
      to"
  unless ← isDefEq (← inferType lemma) tgt do
    err m!"the layer is not the map of its children over{indentExpr s}\nin"
  g.assign lemma
  return goals.toList.map (·.mvarId!)

/--
`qpf_ctor_mono` proves the monotonicity of (the unfolding of) a partial constructor, i.e. a
goal `monotone (fun z => CofixWithBot.mk L[z])`, with the monotonicity of the possibly-partial
arguments in context.
-/
syntax "qpf_ctor_mono" : tactic

open Lean.Order in
macro_rules
  | `(tactic| qpf_ctor_mono) => `(tactic| first
    | assumption
    | exact Lean.Order.monotone_const _
    | (qpf_mk_mono <;> qpf_ctor_mono)
    -- E.g. for other partial constructors, with their `__partial_mono` lemmas. This fails
    -- unless `monotonicity` makes progress.
    | (monotonicity <;> qpf_ctor_mono))

/-- Define `declName.__partial`, see the module docstring. Records the lemmas
`g.__partial_ofCofix` of the partial versions used in its body in `log`. -/
def addPartialCtor (declName : Name) (log : IO.Ref (Array Name)) : MetaM Unit := do
  let info ← getConstInfo declName
  let some value := info.value? (allowOpaque := false)
    | throwError "@[qpf_ctor] can only be applied to definitions, \
        but `{.ofConstName declName}` is not"
  forallTelescope info.type fun xs R => do
    unless ← isCofixType R do
      throwError "@[qpf_ctor]: the result type of `{.ofConstName declName}` should be a \
        `Cofix` type, but it is{indentExpr R}"
    let ctx ← mkCtx declName .anonymous R (log := log)
    let body := (mkAppN value xs).headBeta
    withTranslatedParams ctx declName xs (attr := `qpf_ctor) fun xs' => do
      let body' ← ctx.go (body.replaceFVars xs xs')
      let some body' ← ctx.coerce? body' ctx.PT
        | throwError "@[qpf_ctor]: the translated body of `{.ofConstName declName}`{indentExpr
            body'}\ndoes not have type{indentExpr ctx.PT}"
      addPartialDef (declName ++ partialSuffix) info.levelParams xs' body'

/-- Clean up `e` as `simp only [qpf_productive_by]` would, e.g. reducing the types in the layer
`@StreamF.cons (#t[α] ::: PStream α).head (#t[α] ::: PStream α).tail.head x xs` of
`Stream.cons x xs`, as elaborated against `TypeFun.ofCurried StreamF (#t[α] ::: PStream α)`, to
`@StreamF.cons α (PStream α) x xs`. As with `simp only`, this uses the default simprocs and
those of `qpf_productive_by`. -/
def simpProductiveBy (e : Expr) : MetaM Simp.Result := do
  let some ext ← getSimpExtension? `qpf_productive_by | return { expr := e }
  let ctx ← Simp.mkContext (simpTheorems := #[← ext.getTheorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let mut simprocs := #[← Simp.getSimprocs]
  if let some ext ← Simp.getSimprocExtension? `qpf_productive_by then
    simprocs := simprocs.push (← ext.getSimprocs)
  return (← simp e ctx simprocs).1

/-- The suffix for the lemma `Cofix.dest (g.__partial xs) = Comp.mk (some L)` of a constructor
`g`, see `addPartialCtorDest`. -/
def destPartialSuffix : Name := `__dest_partial

/-- The suffix for the lemma `Comp.get (Cofix.dest (g.__partial xs)) = some L` of a constructor
`g`, see `addPartialCtorDest`. -/
def getDestPartialSuffix : Name := `__get_dest_partial

/-- If `declName.__partial xs` unfolds, at its head, to a layer `CofixWithBot.mk L`, add
* `declName.__dest_partial : Cofix.dest (declName.__partial xs) = Comp.mk (some L)`, and
* `declName.__get_dest_partial : Comp.get (Cofix.dest (declName.__partial xs)) = some L`, which
  simplifies the root of the layer in one step, as found in `HasNoBot` goals,

both marked with `@[simp, qpf_productive_by, grind =]`, the latter as a `simp` pre-lemma (`↓`).
Constructors whose body is not a fixed layer (e.g. an `if`) get no such lemmas. -/
def addPartialCtorDest (declName : Name) : MetaM Unit := do
  let pName := declName ++ partialSuffix
  let pInfo ← getConstInfo pName
  let lvls := pInfo.levelParams.map mkLevelParam
  let destName := declName ++ destPartialSuffix
  let getDestName := declName ++ getDestPartialSuffix
  let added ← forallTelescope pInfo.type fun xs _ => do
    let lhs := mkAppN (.const pName lvls) xs
    -- Unfold the head (e.g. `g.__partial`, or other partial constructors) up to `mk L`.
    let layer ← whnfHeadPred lhs fun e => return !e.isAppOfArity ``QPF.CofixWithBot.mk 5
    unless layer.isAppOfArity ``QPF.CofixWithBot.mk 5 do return false
    -- `mk L` unfolds to `Cofix.mk y`, with `y = Comp.mk (some L)`.
    let some m ← unfoldDefinition? layer | return false
    let m := m.headBeta
    unless m.isAppOfArity ``QPF.Cofix.mk 5 do return false
    let y := m.appArg!
    unless y.isAppOfArity ``QPF.Comp.mk 6 do return false
    -- State the lemmas with the layer cleaned up (see `simpProductiveBy`), composing their
    -- proofs with `simp`'s proof `hL : some L = some L'`.
    let rL ← simpProductiveBy y.appArg!
    let hL ← rL.getProof
    let mkY := y.appFn!
    let addThm (name : Name) (eq proof : Expr) : MetaM Unit := do
      let type ← instantiateMVars (← mkForallFVars xs eq)
      let value ← instantiateMVars (← mkLambdaFVars xs proof)
      unless ← isDefEq (← inferType value) type do
        throwError "@[qpf_ctor]: failed to prove `{.ofConstName name}`"
      addDecl <| .thmDecl { name, levelParams := pInfo.levelParams, type, value }
    let cofixLvls := m.getAppFn.constLevels!
    let dest := mkAppN (.const ``QPF.Cofix.dest cofixLvls) (m.getAppArgs.pop.push lhs)
    let destProof := mkAppN (.const ``QPF.Cofix.dest_mk cofixLvls) m.getAppArgs
    addThm destName (← mkEq dest (mkApp mkY rL.expr))
      (← mkEqTrans destProof (← mkCongrArg mkY hL))
    -- `Comp.get` takes the same implicit arguments as `Comp.mk`, and `get (mk x) = x` holds
    -- by `rfl`.
    let get := mkAppN (.const ``QPF.Comp.get y.getAppFn.constLevels!) y.getAppArgs.pop
    addThm getDestName (← mkEq (mkApp get dest) rL.expr)
      (← mkEqTrans (← mkCongrArg get destProof) hL)
    return true
  if added then
    for name in [destName, getDestName] do
      Attribute.add name `grind (← `(attr| grind =))
    -- Both lemmas go into the default simp set and `qpf_productive_by`, so that the cleanup at
    -- the end of `productive_by_intro` already unfolds the root layer.
    let mut exts := #[simpExtension]
    if let some ext ← getSimpExtension? `qpf_productive_by then exts := exts.push ext
    for ext in exts do
      addSimpTheorem ext destName (post := true) (inv := false) .global (eval_prio default)
      -- So that `simp` rewrites `Comp.get (Cofix.dest (g.__partial xs))` in one step, this is
      -- a pre-lemma (`↓`), which is tried before the subterms are visited: otherwise
      -- `__dest_partial` would already have rewritten `Cofix.dest (g.__partial xs)`.
      addSimpTheorem ext getDestName (post := false) (inv := false) .global (eval_prio default)

initialize registerBuiltinAttribute {
  name := `qpf_ctor
  descr := "define the partial version of a constructor of a coinductive type, for `codef`"
  applicationTime := .afterCompilation
  add := fun declName stx attrKind => do
    Attribute.Builtin.ensureNoArgs stx
    unless attrKind == .global do
      throwError "@[qpf_ctor] can only be used globally"
    let log ← IO.mkRef #[]
    MetaM.run' (addPartialCtor declName log)
    MetaM.run' (addPartialCtorDest declName)
    let pName := declName ++ partialSuffix
    MetaM.run' <| Term.TermElabM.run' do
      addPartialMono `qpf_ctor declName false (← `(tactic| qpf_ctor_mono))
      let step ← mkOfCofixStep (← log.get)
      addPartialOfCofix `qpf_ctor declName <| ← `(tactic|
        (delta $(mkCIdent declName):ident $(mkCIdent pName):ident
         repeat ($step:tactic)
         try rfl))
    Attribute.add (declName ++ partialMonoSuffix) `partial_fixpoint_monotone .missing
  erase := fun declName =>
    throwError "@[qpf_ctor] cannot be erased from '{.ofConstName declName}'"
}

end QPFTypes.Codef
