module

public meta import Lean
public import QPFTypes.Meta.Codef

/-!
# The `@[qpf_elim]` attribute

`codef` translates a corecursive body from a total coinductive type `T = Cofix F α` into the
possibly-partial `PT = CofixWithBot F α` (see `QPFTypes.Meta.Codef`). The results of recursive
calls are then possibly-partial, and cannot be passed to functions which destruct their
argument, such as `Stream.tail (f xs)`: there is no `Cofix.dest` for a possibly-partial value,
since its root may be `⊥`.

Marking such an eliminator `g` with `@[qpf_elim]` defines its partial version `g.__partial`,
which `codef` uses in place of `g` whenever `g` is applied to a possibly-partial value. Every
argument of `g` of type `T` becomes an argument of type `PT`, and every `Cofix.dest x` of such an
argument in the body of `g` is replaced by the root layer `y` of `x`, with the body wrapped in
`CofixWithBot.elim x (fun y => ...)`. Since `elim` sends `⊥` to `⊥`, this needs the result to be
of a `CofixWithBot` type, which gives two forms:

* if the (translated) result type is a `CofixWithBot` type, as for
  `Stream.tail : Stream α → Stream α`, then
  ```
  Stream.tail.__partial (xs : PStream α) : PStream α :=
    CofixWithBot.elim xs fun y => y.2
  ```
* otherwise, as for `Stream.head : Stream α → α`, the partial version is in
  continuation-passing style, into any `CofixWithBot` type:
  ```
  Stream.head.__partial (xs : PStream α) {m G} [QPF G] {β}
      (k : α → CofixWithBot G β) : CofixWithBot G β :=
    CofixWithBot.elim xs fun y => k y.1
  ```
  `codef` does not yet use partial versions of this form.

The attribute also proves the monotonicity lemma `g.__partial_mono`, and registers it with
`@[partial_fixpoint_monotone]`, so that `partial_fixpoint` accepts recursive calls under `g`.
For the direct form, if `g` returns a value of type `T`, it also proves
`g.__partial_ofCofix : ofCofix (g xs) = g.__partial (ofCofix xs)`, which `codef` uses to prove
unfolding equations.

## Limitations

* Only the arguments of type `T` themselves can be destructed, not values obtained from them
  (e.g. `Cofix.dest (Cofix.dest x).2`).
* Arguments whose types depend on an argument of type `T` are not supported.
* The monotonicity proof (`qpf_elim_mono`) relies on projections out of `F`-layers reducing
  definitionally, as they do for functors such as products.
-/

public meta section

namespace QPFTypes.Codef

open Lean Meta Elab

/-- The suffix for the monotonicity lemma of a partial eliminator. -/
def partialMonoSuffix : Name := `__partial_mono

/--
`qpf_reduce_projs` reduces projections (such as `((TypeVec.id ::: g) <$$> s).2`) in the goal
whose structure argument reduces to a constructor, and then reduces the result to weak head
normal form (e.g. `g s.2`).
-/
syntax (name := qpfReduceProjs) "qpf_reduce_projs" : tactic

@[tactic qpfReduceProjs]
def evalQpfReduceProjs : Tactic.Tactic := fun _ => Tactic.liftMetaTactic1 fun g => do
  let t ← instantiateMVars (← g.getType)
  let t' ← Meta.transform t (post := fun e => do
    let e₁ ← match e.getAppFn with
      | .const fn _ =>
        if (← getProjectionFnInfo? fn).isSome then
          pure ((← unfoldDefinition? e).getD e)
        else pure e
      | _ => pure e
    if let .proj .. := e₁ then
      if let some e' ← Meta.reduceProj? e₁ then return .visit (← whnfD e'.headBeta)
    return .continue)
  g.change t'

/--
`qpf_elim_mono` proves the monotonicity of (the unfolding of) a partial eliminator, i.e.
a goal `monotone (fun z => CofixWithBot.elim (x z) (k z))`, with `monotone x` in context.
-/
syntax "qpf_elim_mono" : tactic

open Lean.Order in
macro_rules
  | `(tactic| qpf_elim_mono) => `(tactic| first
    | assumption
    | (apply QPF.CofixWithBot.elim_mono <;> (try intros) <;> qpf_reduce_projs <;> qpf_elim_mono)
    | (apply Lean.Order.monotone_apply; assumption)
    -- `monotonicity` may apply `elim_mono` itself, leaving its premises open.
    | (monotonicity; done))

/-- A universe level name which is not among `lvls`. -/
def freshLevelName (lvls : List Name) (base : String) : Name := Id.run do
  let mut i := 0
  let mut n := Name.mkSimple base
  while lvls.contains n do
    i := i + 1
    n := Name.mkSimple s!"{base}_{i}"
  return n

/-- Whether `ty` unfolds to a `Cofix` type. -/
partial def isCofixType (ty : Expr) : MetaM Bool := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``QPF.Cofix 4 then return true
  match ← unfoldDefinition? ty with
  | some ty => isCofixType ty
  | none => return false

/-- If `ty` is a `CofixWithBot` type (up to unfolding), its universe level, and its arguments
`m G [QPF G] β`. -/
def cofixWithBotArgs? (ty : Expr) : MetaM (Option (Level × Array Expr)) := do
  let lvl ← mkFreshLevelMVar
  let c := Expr.const ``QPF.CofixWithBot [lvl]
  let (args, _, _) ← forallMetaTelescope (← inferType c)
  unless ← isDefEq ty (mkAppN c args) do return none
  return some (← instantiateLevelMVars lvl, ← args.mapM instantiateMVars)

/-- Introduce the parameters `xs` again, with their types translated by `ctx`, and call `k` on
the new parameters. Parameters of type `T` become parameters of type `PT`. -/
def withTranslatedParams (ctx : Ctx) (declName : Name) (xs : Array Expr)
    (k : Array Expr → MetaM α) (i : Nat := 0) (ys : Array Expr := #[]) : MetaM α := do
  if h : i < xs.size then
    let x := xs[i]
    let decl ← x.fvarId!.getDecl
    let ty := decl.type.replaceFVars xs[:i] ys
    let ty' ← ctx.go ty
    if ← xs[:i].toArray.anyM fun z => do
        return decl.type.containsFVar z.fvarId! && (← ctx.isTotalType (← inferType z)) then
      throwError "@[qpf_elim]: the type of the argument `{decl.userName}` of \
        `{.ofConstName declName}` depends on an argument of type{indentExpr ctx.T}"
    -- Keep the parameters whose type does not change (e.g. the parameters of `T`).
    if ty' == decl.type then
      return ← withTranslatedParams ctx declName xs k (i + 1) (ys.push x)
    withLocalDecl decl.userName decl.binderInfo ty' fun y =>
      withTranslatedParams ctx declName xs k (i + 1) (ys.push y)
  else
    k ys

/-- Define `declName.__partial`, see the module docstring, and return whether it is in
continuation-passing style. -/
def addPartialElim (declName : Name) : MetaM Bool := do
  let info ← getConstInfo declName
  let some value := info.value? (allowOpaque := false)
    | throwError "@[qpf_elim] can only be applied to definitions, \
        but `{.ofConstName declName}` is not"
  let lvlNames := info.levelParams
  forallTelescope info.type fun xs R => do
    let body := (mkAppN value xs).headBeta
    let some x₀ ← xs.findM? fun x => do isCofixType (← inferType x)
      | throwError "@[qpf_elim]: `{.ofConstName declName}` has no argument of a `Cofix` type"
    let ctx ← mkCtx declName .anonymous (← inferType x₀)
    withTranslatedParams ctx declName xs fun xs' => do
      -- The root layers `y` of the possibly-partial arguments.
      let lifted ← (xs.zip xs').filterM fun (x, _) => do ctx.isTotalType (← inferType x)
      let rec withRoots {γ : Type} (i : Nat) (dests : Array (Expr × Expr))
          (k : Array (Expr × Expr) → MetaM γ) : MetaM γ := do
        if h : i < lifted.size then
          let (x, x') := lifted[i]
          let yTy ← ctx.go (← inferType (mkApp (ctx.mkConst ``QPF.Cofix.dest) x))
          withLocalDeclD `y yTy fun y => withRoots (i + 1) (dests.push (x', y)) k
        else k dests
      withRoots 0 #[] fun dests => do
        let ctx := { ctx with dests }
        let body' ← ctx.go (body.replaceFVars xs xs')
        let R' ← ctx.go (R.replaceFVars xs xs')
        let used := dests.filter fun (_, y) => body'.containsFVar y.fvarId!
        if used.isEmpty then
          throwError "@[qpf_elim]: `{.ofConstName declName}` does not destruct any of its \
            arguments of type{indentExpr ctx.T}"
        let pName := declName ++ partialSuffix
        -- `elim x₁ fun y₁ => ... elim xₙ fun yₙ => b`, into `CofixWithBot.{lvl} gArgs`.
        let wrap (lvl : Level) (gArgs : Array Expr) (b : Expr) : MetaM Expr :=
          used.foldrM (init := b) fun (x', y) b => do
            let e := mkAppN (.const ``QPF.CofixWithBot.elim [ctx.lvl, lvl])
              (ctx.args ++ gArgs ++ #[x', ← mkLambdaFVars #[y] b])
            try check e
            catch ex => throwError "@[qpf_elim]: failed to construct `{.ofConstName pName}`:\
              {indentD ex.toMessageData}"
            return e
        let addDef (lvls : List Name) (params : Array Expr) (value : Expr) : MetaM Unit := do
          let value ← instantiateMVars (← mkLambdaFVars params value)
          let type ← instantiateMVars (← inferType value)
          addAndCompile <| .defnDecl {
            name := pName, levelParams := lvls, type, value
            hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe
          }
          -- So that its equation lemmas (e.g. for `unfold`) can be generated on demand.
          enableRealizationsForConst pName
        -- The direct form, if the result type is a `CofixWithBot` type.
        if let some (lvl, gArgs) ← cofixWithBotArgs? R' then
          addDef lvlNames xs' (← wrap lvl gArgs body')
          return false
        -- Otherwise, the continuation-passing form.
        let v := freshLevelName lvlNames "v"
        let elimTy ← instantiateForall
          (← inferType (.const ``QPF.CofixWithBot.elim [ctx.lvl, .param v])) ctx.args
        forallBoundedTelescope elimTy (some 4) fun gs rest => do
          -- `rest` is `(x : PT) → (k : _ → CofixWithBot G β) → CofixWithBot G β`.
          let cod := rest.bindingBody!.bindingBody!
          withLocalDeclD `k (← mkArrow R' cod) fun k => do
            addDef (lvlNames ++ [v]) (xs' ++ gs ++ #[k]) (← wrap (.param v) gs (mkApp k body'))
            return true

/-- Prove and add `declName.__partial_mono`, see the module docstring. -/
def addPartialElimMono (declName : Name) (cps : Bool) : TermElabM Unit := do
  let pName := declName ++ partialSuffix
  let pInfo ← getConstInfo pName
  let lvlNames := pInfo.levelParams
  let w := freshLevelName lvlNames "w"
  forallTelescope pInfo.type fun ps _ => do
    let nParams := if cps then ps.size - 5 else ps.size
    let params := ps[:nParams].toArray
    -- `withTranslatedParams` gave the possibly-partial arguments the type `PT` literally.
    let PTs ← params.filterM fun p => return (← inferType p).getAppFn.isConstOf ``QPF.CofixWithBot
    withLocalDecl `δ .implicit (.sort (.param w)) fun δ => do
    withLocalDecl `inst .instImplicit (← mkAppM ``Lean.Order.PartialOrder #[δ]) fun instδ => do
    withLocalDeclD `z δ fun z => do
    -- Each possibly-partial argument `p` becomes a monotone function `x : δ → PT`.
    let rec withFns {γ : Type} (i : Nat) (fns hs : Array Expr)
        (k : Array Expr → Array Expr → TermElabM γ) : TermElabM γ := do
      if h : i < PTs.size then
        let p := PTs[i]
        withLocalDeclD ((← p.fvarId!.getUserName).appendAfter "_fn")
            (← mkArrow δ (← inferType p)) fun x => do
          withLocalDeclD `hx (← mkAppM ``Lean.Order.monotone #[x]) fun hx =>
            withFns (i + 1) (fns.push x) (hs.push hx) k
      else k fns hs
    withFns 0 #[] #[] fun fns hs => do
      let args := params.map fun p =>
        match PTs.idxOf? p with
        | some i => mkApp fns[i]! z
        | none => p
      let finish (extra : Array Expr) (args : Array Expr) : TermElabM Unit := do
        let lhs ← mkLambdaFVars #[z] (mkAppN (.const pName (lvlNames.map mkLevelParam)) args)
        let goal ← mkAppM ``Lean.Order.monotone #[lhs]
        let g ← mkFreshExprSyntheticOpaqueMVar goal
        let tac ← `(tactic| (unfold $(mkCIdent pName):ident; qpf_elim_mono))
        let gs ← try Tactic.run g.mvarId! (Tactic.evalTactic tac)
          catch ex => throwError "@[qpf_elim]: failed to prove the monotonicity of \
            `{.ofConstName pName}`:{indentD ex.toMessageData}"
        unless gs.isEmpty do
          throwError "@[qpf_elim]: failed to prove the monotonicity of `{.ofConstName pName}`, \
            unsolved goals:{goalsToMessageData gs}"
        let otherParams := params.filter (!PTs.contains ·)
        let binders := #[δ, instδ] ++ otherParams ++ fns ++ hs ++ extra
        let type ← instantiateMVars (← mkForallFVars binders goal)
        let value ← instantiateMVars (← mkLambdaFVars binders g)
        addDecl <| .thmDecl {
          name := declName ++ partialMonoSuffix
          levelParams := lvlNames ++ [w]
          type, value
        }
      if cps then
        -- `{m G} [QPF G] {β}`, and the continuation `k`, which becomes `k : δ → _ → _`.
        let gs := ps[nParams:nParams + 4].toArray
        let k := ps[nParams + 4]!
        -- `IsPolynomial G`, for the instance `QPF G` in `gs`.
        let qpfTy ← inferType gs[2]!
        let isPolyTy := mkAppN (.const ``QPF.IsPolynomial qpfTy.getAppFn.constLevels!)
          (qpfTy.getAppArgs.push gs[2]!)
        withLocalDecl `inst .instImplicit isPolyTy fun instG => do
        withLocalDeclD `k_fn (← mkArrow δ (← inferType k)) fun kf => do
        withLocalDeclD `hk (← mkAppM ``Lean.Order.monotone #[kf]) fun hk => do
          finish (gs ++ #[instG, kf, hk]) (args ++ gs ++ #[mkApp kf z])
      else
        finish #[] args

/-- If `declName` returns a value of the same type `T` that it destructs, prove and add
`declName.__partial_ofCofix : ofCofix (g xs) = g.__partial (ofCofix xs)`, which `codef` uses
to prove unfolding equations, see `Codef.addUnfoldEqns`. -/
def addPartialElimOfCofix (declName : Name) : TermElabM Unit := do
  let info ← getConstInfo declName
  let pName := declName ++ partialSuffix
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs R => do
    let some x₀ ← xs.findM? fun x => do isCofixType (← inferType x) | return
    let ctx ← mkCtx declName .anonymous (← inferType x₀)
    unless ← ctx.isTotalType R do return
    let ofCofix := ctx.mkConst ``QPF.CofixWithBot.ofCofix
    let args ← xs.mapM fun x => do
      return if ← ctx.isTotalType (← inferType x) then mkApp ofCofix x else x
    let rhs := mkAppN (.const pName lvls) args
    -- Only if `g.__partial` takes the other arguments unchanged.
    unless (← observing? (check rhs)).isSome do return
    let goal ← mkEq (mkApp ofCofix (mkAppN (.const declName lvls) xs)) rhs
    let g ← mkFreshExprSyntheticOpaqueMVar goal
    let tac ← `(tactic|
      (delta $(mkCIdent pName):ident
       simp only [$(mkCIdent ``QPF.CofixWithBot.elim_ofCofix):ident]
       try rfl))
    let gs ← try Tactic.run g.mvarId! (Tactic.evalTactic tac)
      catch ex => throwError "@[qpf_elim]: failed to prove `{.ofConstName pName}` commutes \
        with `ofCofix`:{indentD ex.toMessageData}"
    unless gs.isEmpty do
      throwError "@[qpf_elim]: failed to prove `{.ofConstName pName}` commutes with \
        `ofCofix`, unsolved goals:{goalsToMessageData gs}"
    addDecl <| .thmDecl {
      name := declName ++ partialOfCofixSuffix
      levelParams := info.levelParams
      type := ← mkForallFVars xs goal
      value := ← instantiateMVars (← mkLambdaFVars xs g)
    }

initialize registerBuiltinAttribute {
  name := `qpf_elim
  descr := "define the partial version of an eliminator of a coinductive type, for `codef`"
  applicationTime := .afterCompilation
  add := fun declName stx attrKind => do
    Attribute.Builtin.ensureNoArgs stx
    unless attrKind == .global do
      throwError "@[qpf_elim] can only be used globally"
    let cps ← MetaM.run' (addPartialElim declName)
    MetaM.run' <| Term.TermElabM.run' do
      addPartialElimMono declName cps
      addPartialElimOfCofix declName
    Attribute.add (declName ++ partialMonoSuffix) `partial_fixpoint_monotone .missing
  erase := fun declName =>
    throwError "@[qpf_elim] cannot be erased from '{.ofConstName declName}'"
}

end QPFTypes.Codef
