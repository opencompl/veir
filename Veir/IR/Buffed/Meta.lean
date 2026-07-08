module

public import Veir.IR.Buffed.SimDefs
public import Lean


open Lean Meta

public section

register_grind_attr generic_ptr_grind
register_grind_attr inbounds

@[noinline]
def Option.specGet {α} (x : Option α) (h : x.isSome) : α :=
  x.get h

@[noinline, expose, grind]
def Option.specGet! {α} [Inhabited α] (x : Option α) : α :=
  x.get!

attribute [grind .] Option.ne_none_iff_isSome Option.some_get!

@[grind .]
theorem Option.maybe₁_and_isSome {α} [Inhabited α] (x : Option α) (P : α → Prop) :
    x.maybe₁ P → x.isSome → P x.get! := by
  cases x <;> grind

@[grind .]
theorem Option.maybe_and_isSome_get! {α} [Inhabited α] (x : Option α) (P : α → β → Prop) :
    x.maybe P y → x.isSome → P x.get! y := by
  cases x <;> grind

@[grind .]
theorem Option.maybe_and_isSome_specGet! {α} [Inhabited α] (x : Option α) (P : α → β → Prop) :
    x.maybe P y → x.isSome → P x.specGet! y := by
  sorry

theorem Veir.Sim.IRContext.option_ext [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] (x y : Option (Veir.Sim.IRContext OpInfo)) :
    (x.map (·.spec) = y.map (·.spec) ∧ x.map (·.buf) = y.map (·.buf)) → x = y := by
  cases x <;> cases y <;> grind [cases Sim.IRContext]

end

namespace Veir.Buffed

private meta def checkSim (n : Name) : AttrM Unit :=
  match n with
  | .str _ s =>
    unless s.endsWith "Sim" do
      throwError "@[buffed] can only be applied to declarations with a `Sim` suffix"
  | _ =>
    throwError "@[buffed] can only be applied to declarations with a `Sim` suffix"

/--
Replace a trailing `Sim` suffix on `n`'s final component with `suffix` (appending `suffix` if there
is no `Sim` to drop). With `suffix := ""` this strips the `Sim`, e.g. `fooSim ↦ foo`.
-/
private meta def renameSim (suffix : String) (n : Name) : Name :=
  match n with
  | .str p s =>
      let base := if s.endsWith "Sim" then (s.dropEnd 3).toString else s
      if suffix.isEmpty then .str p base else .str p (base ++ suffix)
  | _ => if suffix.isEmpty then n else .str n suffix

/-- Turn `fooSim` into `fooImpl` (or append `Impl` when no `Sim` suffix). -/
private meta def mkImplName : Name → Name := renameSim "Impl"

/-- Turn `fooSim` into `fooSpec` (or append `Spec` when no `Sim` suffix). -/
private meta def mkSpecName : Name → Name := renameSim "Spec"

/-- Turn `fooSim` into `foo` (or keep name unchanged when no `Sim` suffix). -/
private meta def mkBaseName : Name → Name := renameSim ""

/-- Turn `fooSim` into `foo_def` (the name of the generated `rfl` lemma relating `foo` to `fooSim`). -/
private meta def mkDefName : Name → Name := renameSim "_def"

/-- Turn `fooSim` into `foo_impl` (the name of the generated lemma relating `(fooSim …).impl` to
`fooImpl` applied to the projected arguments). -/
private meta def mkImplLemmaName : Name → Name := renameSim "_impl"

/-- Table entry describing how to split/rebuild a structured argument. -/
private structure BuffedSplitRule where
  typeName : Name
  ctorName : Name
  fieldSuffixes : Array String

/-- Build a plain two-field `impl`/`spec` split rule for the structure `typeName`/`ctorName`. -/
private meta def implSpecRule (typeName ctorName : Name) : BuffedSplitRule :=
  { typeName, ctorName, fieldSuffixes := #["impl", "spec"] }

/--
Known structures that `@[buffed]` should split into field arguments. `IRContext` is special — three
fields, the last a `sim` proof — while every other entry is a plain two-field `impl`/`spec` pair.
-/
private meta def buffedSplitTable : Array BuffedSplitRule :=
  #[{ typeName := ``Veir.Sim.IRContext
      ctorName := ``Veir.Sim.IRContext.mk
      fieldSuffixes := #["buf", "spec", "sim"] }]
    ++ #[
      implSpecRule ``Veir.Sim.OperationPtr ``Veir.Sim.OperationPtr.mk,
      implSpecRule ``Veir.Sim.OptionOperationPtr ``Veir.Sim.OptionOperationPtr.mk,
      implSpecRule ``Veir.Sim.BlockPtr ``Veir.Sim.BlockPtr.mk,
      implSpecRule ``Veir.Sim.OptionBlockPtr ``Veir.Sim.OptionBlockPtr.mk,
      implSpecRule ``Veir.Sim.RegionPtr ``Veir.Sim.RegionPtr.mk,
      implSpecRule ``Veir.Sim.OptionRegionPtr ``Veir.Sim.OptionRegionPtr.mk,
      implSpecRule ``Veir.Sim.OpResultPtr ``Veir.Sim.OpResultPtr.mk,
      implSpecRule ``Veir.Sim.BlockArgumentPtr ``Veir.Sim.BlockArgumentPtr.mk,
      implSpecRule ``Veir.Sim.OpOperandPtr ``Veir.Sim.OpOperandPtr.mk,
      implSpecRule ``Veir.Sim.OptionOpOperandPtr ``Veir.Sim.OptionOpOperandPtr.mk,
      implSpecRule ``Veir.Sim.BlockOperandPtr ``Veir.Sim.BlockOperandPtr.mk,
      implSpecRule ``Veir.Sim.OptionBlockOperandPtr ``Veir.Sim.OptionBlockOperandPtr.mk,
      implSpecRule ``Veir.Sim.ValuePtr ``Veir.Sim.ValuePtr.mk,
      implSpecRule ``Veir.Sim.OpOperandPtrPtr ``Veir.Sim.OpOperandPtrPtr.mk,
      implSpecRule ``Veir.Sim.BlockOperandPtrPtr ``Veir.Sim.BlockOperandPtrPtr.mk
    ]

/-- Find the split rule for a structure head constant, if any. -/
private meta def findBuffedSplitRule? (typeName : Name) : Option BuffedSplitRule :=
  buffedSplitTable.find? (fun r => r.typeName == typeName)

/-- The split rule for `e`'s head constant (`anonymous` when `e` is not an application of a constant). -/
private meta def splitRuleOf? (e : Expr) : Option BuffedSplitRule :=
  findBuffedSplitRule? (e.getAppFn.constName?.getD .anonymous)

/--
Whether `e`'s head constant is `Sim.IRContext` or a structure in the split table — i.e. a type that
`@[buffed]` splits into `impl`/`spec` fields. A *non-split* leaf (e.g. `UInt64`) carries no spec: the
`Sim` value *is* its impl, so impl/spec projections and the impl/spec recombination are all the
identity, and the base wrapper just returns `<name>Impl`.
-/
private meta def isSplitType (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some ``Veir.Sim.IRContext => true
  | some n => (findBuffedSplitRule? n).isSome
  | none => false

/-- If `e` is `C a₁ … aₙ` for the given constant `C` and arity `n`, return its argument array. -/
private meta def appOf? (c : Name) (arity : Nat) (e : Expr) : Option (Array Expr) :=
  if e.getAppFn.constName? == some c && e.getAppArgs.size == arity then
    some e.getAppArgs
  else
    none

/-- Expand Sim-structured arguments into the flattened argument list expected by `<name>Impl`. With
`named := true` the per-field projections are the *named* `arg.<field>` form (for the `_impl` lemma
statement); otherwise they are the raw indexed `mkProj` used when defining the base wrapper. -/
private meta def mkImplArgsFrom (args : Array Expr) (named : Bool := false) : MetaM (Array Expr) := do
  let mut implArgs := #[]
  for arg in args do
    let argTyWhnf ← whnf (← inferType arg)
    match argTyWhnf.getAppFn.constName?, splitRuleOf? argTyWhnf with
    | some typeName, some rule =>
        let fieldNames? ← if named then pure ((getStructureInfo? (← getEnv) typeName).map (·.fieldNames)) else pure none
        for i in [0:rule.fieldSuffixes.size] do
          match fieldNames? with
          | some fieldNames => implArgs := implArgs.push (← mkProjection arg fieldNames[i]!)
          | none => implArgs := implArgs.push (mkProj typeName i arg)
    | _, _ =>
        implArgs := implArgs.push arg
  pure implArgs

/--
Project field `fieldIdx` (0 = `impl`, 1 = `spec`) out of `e`, descending through `Option` and `Prod`
to reach the underlying split type. Example (`fieldIdx = 0`):

    e : Option (Sim.BlockPtr × Sim.RegionPtr)
    ⊢ e.map fun x => (x.1.impl, x.2.impl)
-/
private meta partial def mkBuffedProj (fieldIdx : Nat) (e : Expr) (named : Bool := false) : MetaM Expr := do
  let eTy ← whnf (← inferType e)
  if let some #[innerTy] := appOf? ``Option 1 eTy then
    withLocalDeclD `_x innerTy fun x => do
      let projFn ← mkLambdaFVars #[x] (← mkBuffedProj fieldIdx x named)
      mkAppM ``Option.map #[projFn, e]
  else if (appOf? ``Prod 2 eTy).isSome then
    let fst ← mkBuffedProj fieldIdx (← mkAppM ``Prod.fst #[e]) named
    let snd ← mkBuffedProj fieldIdx (← mkAppM ``Prod.snd #[e]) named
    mkAppM ``Prod.mk #[fst, snd]
  else if (appOf? ``Sigma 2 eTy).isSome then
    -- Dependent pair: project each component, then re-pack with an explicit type family. Any split
    -- dependency lives only in the ghost/`spec` data, so the impl projection's second-component type
    -- does not actually mention the first — but we abstract it out anyway (via `kabstract`) to stay
    -- correct if it ever does.
    let fst ← mkBuffedProj fieldIdx (← mkAppM ``Sigma.fst #[e]) named
    let snd ← mkBuffedProj fieldIdx (← mkAppM ``Sigma.snd #[e]) named
    -- `β := fun a' => (type of snd)[fst := a']`, the type family of the rebuilt `Sigma`.
    let fstTy ← inferType fst
    let sndTy ← inferType snd
    let β := Expr.lam `_a fstTy (← kabstract sndTy fst) .default
    -- `Sigma.mk`'s `α`/`β` are implicit; pass them explicitly and let `mkAppOptM` infer universes.
    mkAppOptM ``Sigma.mk #[some fstTy, some β, some fst, some snd]
  else if !isSplitType eTy then
    -- Non-split leaf (e.g. `UInt64`): no spec to drop, so both projections are the identity.
    pure e
  else
    let some typeName := eTy.getAppFn.constName?
      | throwError "@[buffed]: expected a known split type, got {eTy}"
    let some rule := findBuffedSplitRule? typeName
      | throwError "@[buffed]: no split rule registered for {typeName}"
    if fieldIdx < rule.fieldSuffixes.size then
      -- `named` selects the displayed form: `mkProjection` builds the named projection `e.<field>`
      -- (for the `_impl` lemma *statement*), while `mkProj` is the raw indexed projection used when
      -- *defining* `<name>Impl`/`<name>Spec`/base.
      if named then
        let some sInfo := getStructureInfo? (← getEnv) typeName
          | throwError "@[buffed]: expected a structure type for {typeName}"
        mkProjection e sInfo.fieldNames[fieldIdx]!
      else
        pure (mkProj typeName fieldIdx e)
    else
      throwError "@[buffed]: field index {fieldIdx} out of bounds for {typeName}"

/--
Re-project then reassemble `e` (definitionally equal to it), descending through `Option`, `Prod`, and
dependent `Sigma`. Each split type is rebuilt by re-applying its constructor to its fields, so the
result is phrased in the impl/spec-split shape of the generated `<name>Impl`/`<name>Spec`. Example:

    e : Option Sim.BlockPtr
    ⊢ e.bind fun x => some ⟨x.impl, x.spec⟩
-/
private meta partial def mkBuffedRebuild (e : Expr) : MetaM Expr := do
  let eTy ← whnf (← inferType e)
  if let some #[innerTy] := appOf? ``Option 1 eTy then
    withLocalDeclD `_x innerTy fun x => do
      let someRebuilt ← mkAppM ``Option.some #[← mkBuffedRebuild x]
      let bindFn ← mkLambdaFVars #[x] someRebuilt
      mkAppM ``Option.bind #[e, bindFn]
  else if (appOf? ``Prod 2 eTy).isSome then
    let fst ← mkBuffedRebuild (← mkAppM ``Prod.fst #[e])
    let snd ← mkBuffedRebuild (← mkAppM ``Prod.snd #[e])
    mkAppM ``Prod.mk #[fst, snd]
  else if let some #[α, β] := appOf? ``Sigma 2 eTy then
    -- Dependent pair: the second component's type mentions the first, so we keep `Sigma`'s
    -- type family `β` explicit instead of letting `mkAppM` infer it.
    let fst ← mkBuffedRebuild (← mkAppM ``Sigma.fst #[e])
    let snd ← mkBuffedRebuild (← mkAppM ``Sigma.snd #[e])
    pure (mkAppN (mkConst ``Sigma.mk eTy.getAppFn.constLevels!) #[α, β, fst, snd])
  else if !isSplitType eTy then
    -- Non-split leaf (e.g. `UInt64`): nothing to take apart, so leave the value as is.
    pure e
  else
    let some typeName := eTy.getAppFn.constName?
      | throwError "@[buffed]: expected a known split type, got {eTy}"
    let some rule := findBuffedSplitRule? typeName
      | throwError "@[buffed]: no split rule registered for return type {typeName}"
    let fields := (Array.range rule.fieldSuffixes.size).map (fun i => mkProj typeName i e)
    mkAppM rule.ctorName fields

/-- Build the generated `<name>Impl` declaration from the original Sim-level definition. -/
meta def buildBuffedImpl (declName : Name) : MetaM (Name × Expr × Expr × List Name) := do
  let info ← getConstInfo declName
  let implName := mkImplName declName
  let us := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun xs _ => do
    let rec go (remaining : List Expr) (oldFVars : Array Expr) (subs : Array Expr) (newLocals : Array Expr) : MetaM (Expr × Expr) := do
      match remaining with
      | [] =>
        let call := mkAppN (mkConst declName us) subs
        let implBody ← mkBuffedProj 0 call
        let implTy ← inferType implBody
        let implForall ← mkForallFVars newLocals implTy
        let implLambda ← mkLambdaFVars newLocals implBody
        pure (implForall, implLambda)
      | x :: rest =>
        let xDecl ← x.fvarId!.getDecl
        -- Update binder type under previously introduced split locals.
        let xTy := xDecl.type.replaceFVars oldFVars subs
        let xTyWhnf ← whnf xTy
        let some typeName := xTyWhnf.getAppFn.constName?
          | withLocalDecl xDecl.userName xDecl.binderInfo xTy fun y =>
              go rest (oldFVars.push x) (subs.push y) (newLocals.push y)
        let some rule := findBuffedSplitRule? typeName
          | withLocalDecl xDecl.userName xDecl.binderInfo xTy fun y =>
              go rest (oldFVars.push x) (subs.push y) (newLocals.push y)
        let some sInfo := getStructureInfo? (← getEnv) typeName
          | throwError "@[buffed]: expected a structure type for {typeName}"
        if rule.fieldSuffixes.size != sInfo.fieldNames.size then
          throwError "@[buffed]: split table field count mismatch for {typeName}"
        let ctorInfo ← getConstInfo rule.ctorName
        let ctorType := ctorInfo.type
        let tyArgs := xTyWhnf.getAppArgs

        let baseName := xDecl.userName.toString
        forallTelescopeReducing ctorType fun ctorXs _ => do
          let fieldCount := rule.fieldSuffixes.size
          if ctorXs.size < fieldCount then
            throwError "@[buffed]: constructor {rule.ctorName} has fewer binders than expected"
          let paramCount := ctorXs.size - fieldCount
          if tyArgs.size < paramCount then
            throwError "@[buffed]: type argument mismatch for {typeName}"
          let ctorParams := ctorXs.extract 0 paramCount
          let ctorFields := ctorXs.extract paramCount ctorXs.size
          let structParams := tyArgs.extract 0 paramCount

          -- Introduce one local per field and thread dependencies left-to-right.
          let rec mkSplitLocals
              (i : Nat)
              (fields : Array Expr)
              (accLocals : Array Expr)
              (k : Array Expr → Array Expr → MetaM (Expr × Expr)) : MetaM (Expr × Expr) := do
            if h : i < rule.fieldSuffixes.size then
              let suffix := rule.fieldSuffixes[i]!
              let fldTpl := ctorFields[i]!
              let fldDecl ← fldTpl.fvarId!.getDecl
              -- Field i may depend on constructor params and earlier fields.
              let fldTy := fldDecl.type.replaceFVars
                (ctorParams ++ ctorFields.extract 0 i)
                (structParams ++ fields)
              -- Spec fields are ghost (erased) data; prefix them with `GHOST_` so the generated
              -- `<name>Impl` parameter names (e.g. `GHOST_ctx_spec`) flag them as such.
              let fldName := Name.mkSimple <|
                if suffix == "spec" then s!"GHOST_{baseName}_{suffix}" else s!"{baseName}_{suffix}"
              withLocalDecl fldName .default fldTy fun fld =>
                mkSplitLocals (i + 1) (fields.push fld) (accLocals.push fld) k
            else
              k fields accLocals

          mkSplitLocals 0 #[] #[] fun fields splitLocals => do
            -- Rebuild the original structured argument from split locals.
            let xReplacement := mkAppN (mkConst rule.ctorName) (structParams ++ fields)
            go rest (oldFVars.push x) (subs.push xReplacement) (newLocals ++ splitLocals)
    let res ← go xs.toList #[] #[] #[]
    let implType := res.1
    let implValue := res.2
    pure (implName, implType, implValue, info.levelParams)

/-- Build the generated `<name>Spec` declaration from the original Sim-level definition. -/
meta def buildBuffedSpec (declName : Name) : MetaM (Name × Expr × Expr × List Name) := do
  let info ← getConstInfo declName
  let specName := mkSpecName declName
  let us := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun xs _ => do
    let call := mkAppN (mkConst declName us) xs
    let specBody ← mkBuffedProj 1 call
    let specTy ← inferType specBody
    let specForall ← mkForallFVars xs specTy
    let specLambda ← mkLambdaFVars xs specBody
    pure (specName, specForall, specLambda, info.levelParams)

/--
Classification of the return type of a Sim-level definition, telling `buildBuffedBase` how to
reassemble the result from the generated `<name>Impl`/`<name>Spec` calls.
-/
private inductive BaseReturnShape where
  /-- Bare `Sim.IRContext …`: rebuild `⟨buf, spec, sim⟩`, carrying the original `sim` proof along. -/
  | irContext
  /-- Bare two-field split type: apply the constructor to the impl/spec calls. -/
  | bareSplit (rule : BuffedSplitRule)
  /-- `Option <impl/spec split>`: drive `some`/`none` off the impl, recover the spec in `some`. -/
  | optionSplit (rule : BuffedSplitRule)
  /-- `Option (Sim.IRContext …)`: like `optionSplit`, but rebuild `IRContext` (with a `sorry` sim). -/
  | optionIRContext (innerTy : Expr)
  /-- Everything else (`Prod`, dependent `Sigma`): re-project and rebuild the original call. -/
  | other

/-- Classify `callTy` (the whnf'd return type of the Sim definition). -/
private meta def classifyReturn (callTy : Expr) : MetaM BaseReturnShape := do
  if callTy.getAppFn.constName? == some ``Veir.Sim.IRContext then
    return .irContext
  if let some rule := splitRuleOf? callTy then
    return .bareSplit rule
  if let some #[inner] := appOf? ``Option 1 callTy then
    let innerWhnf ← whnf inner
    if innerWhnf.getAppFn.constName? == some ``Veir.Sim.IRContext then
      return .optionIRContext innerWhnf
    -- `IRContext` (three fields, a `sim` proof) is handled above; only plain `impl`/`spec` pairs
    -- have the two-argument constructor `optionSplit` relies on.
    if let some rule := splitRuleOf? innerWhnf then
      if rule.fieldSuffixes == #["impl", "spec"] then
        return .optionSplit rule
  return .other

/--
Unwrap `o : Option α` as `o.specGet!` (i.e. `o.get!`), e.g. `o ⊢ o.specGet!`. We use
`Option.get` (a pure projection that reduces to `x` on `some x`) rather than `Option.get!` so the
impl projection drops the spec cleanly instead of keeping a panicking `Inhabited` default alive; the
caller only evaluates this in a `some` branch, so the `isSome` obligation is discharged by `sorry`.
-/
private meta def mkOptionGetSorry (o : Expr) : MetaM Expr := do
  mkAppM ``Option.specGet! #[o]

/--
Build `IRContext.mk buf spec sim : targetTy`, leaving the erased `sim` proof as `sorry`, e.g.

    targetTy = Sim.IRContext OpInfo inst,  buf,  spec
    ⊢ Sim.IRContext.mk buf spec ⋯

The type arguments come from `targetTy`. Lets the base wrapper rebuild `Option (IRContext …)` results
from `<name>Impl`/`<name>Spec` without mentioning `<name>Sim`.
-/
private meta def rebuildIRContextWithSorrySim (targetTy buf spec : Expr) : MetaM Expr := do
  -- `IRContext.mk`'s leading implicit args mirror `Sim.IRContext`'s own parameters (`OpInfo`, `inst`),
  -- so we copy exactly those from `targetTy` rather than hard-coding their count.
  let tyArgs := targetTy.getAppArgs
  let irContextInfo ← getConstInfo ``Veir.Sim.IRContext
  let numParams ← forallTelescopeReducing irContextInfo.type fun xs _ => pure xs.size
  unless tyArgs.size == numParams do
    throwError "@[buffed]: unexpected IRContext type {targetTy}"
  -- Partial application up to (but not including) the `sim` proof; infer its type, fill with `sorry`.
  let mkConstE := mkConst ``Veir.Sim.IRContext.mk targetTy.getAppFn.constLevels!
  let partialApp := mkAppN mkConstE (tyArgs ++ #[buf, spec])
  let simTy := (← whnf (← inferType partialApp)).bindingDomain!
  return mkApp partialApp (← mkSorry simTy (synthetic := true))

/--
Build `IRContext.mk buf spec <proof> : targetTy` where the `sim` proof is *proven* (not `sorry`) from
the `<name>_impl` lemma, for a recursive bare-`IRContext`-returning def. With
`buf := <name>Impl (projected xs)` and `spec := <name>Spec xs`, the `sim` goal `Sim ⟨buf, spec⟩` is
discharged with the template proof (cf. `Rewriter.initOpOperands_example`):

    simp only [← <name>_impl xs, <name>Spec]
    exact (<name>Sim xs).sim

`← <name>_impl xs` rewrites `buf` back to `(<name>Sim xs).buf`; `<name>Spec` unfolds `spec` to
`(<name>Sim xs).spec`; the result is exactly the type of `(<name>Sim xs).sim`. If the proof fails it
emits a warning and falls back to `sorry` (so `buffed` never breaks the build). Requires the
`<name>_impl` lemma to have been emitted already.
-/
private meta def rebuildIRContextWithProvenSim (declName : Name) (us : List Level) (xs : Array Expr)
    (targetTy buf spec : Expr) : Lean.Elab.TermElabM Expr := do
  let tyArgs := targetTy.getAppArgs
  let irContextInfo ← getConstInfo ``Veir.Sim.IRContext
  let numParams ← forallTelescopeReducing irContextInfo.type fun ys _ => pure ys.size
  unless tyArgs.size == numParams do
    throwError "@[buffed]: unexpected IRContext type {targetTy}"
  let mkConstE := mkConst ``Veir.Sim.IRContext.mk targetTy.getAppFn.constLevels!
  let partialApp := mkAppN mkConstE (tyArgs ++ #[buf, spec])
  let simTy := (← whnf (← inferType partialApp)).bindingDomain!
  -- `<name>_impl xs` and `<name>Spec` as simp lemmas; `(<name>Sim xs).sim` as the closing term.
  let implLemma := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let simProj := mkProj ``Veir.Sim.IRContext 2 (mkAppN (mkConst declName us) xs)
  -- Feed the lemma application / spec constant to `simp only` as terms, and close with the `sim`
  -- projection of the `Sim`-level call. If anything fails, fall back to `sorry`.
  let attempt : Lean.Elab.TermElabM (Option Expr) := do
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar simTy
    let remaining ← Lean.Elab.Tactic.run goalMVar.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        simp only [← $(← Lean.PrettyPrinter.delab implLemma):term, $(mkIdent (mkSpecName declName)):ident]))
      Lean.Elab.Tactic.closeMainGoal `buffed simProj
    if remaining.isEmpty then
      pure (some (← instantiateMVars goalMVar))
    else
      pure none
  let proof ←
    match ← (try attempt catch _ => pure none) with
    | some p => pure p
    | none =>
      logWarning m!"@[buffed]: could not prove the `sim` field of the base wrapper for {declName}; \
        falling back to `sorry`"
      mkSorry simTy (synthetic := true)
  return mkApp partialApp proof

/--
Build the *whole* base body for an `Option (IRContext …)`-returning non-recursive def as a `match` on
`<name>Impl …`, with the `sim` proof *proven* (not `sorry`), avoiding the `Subtype`-projection-over-
erased-`attach`-wrapper shape entirely:

    match h : <name>Impl (projected xs) with
    | none     => none
    | some buf => some (Sim.IRContext.mk buf (<name>Spec xs).specGet! (by
        have := <name>_impl xs
        have := (<name>Sim xs).specGet!.sim
        cases _ : <name>Sim xs <;> grind [<name>Spec, Option.specGet!]))

`match h :` compiles (unlike a raw `Option.rec`) via a generated matcher, and the `some buf` branch's
`sim` goal `Sim ⟨buf, (<name>Spec xs).specGet!⟩` is discharged by the template proof: `<name>_impl xs`
relates `<name>Impl …` to `Option.map (·.buf) (<name>Sim xs)` — forcing `<name>Sim xs = some v` with
`v.buf = buf` — and `.specGet!.sim` plus `<name>Spec` (the spec is `(<name>Spec xs).specGet!`) let
`grind` close it after the `cases` `some`/`none` split. The match discriminant / spec value / `<name>_impl`
lemma are delaborated to terms (so the autoParam args on `<name>_impl` stay pinned) and the `match` is
elaborated against the expected `Option (IRContext …)` type. Requires the `<name>_impl` lemma to have been
emitted (and proven) already. `implBody`/`specBody` are the `MetaM`-built `<name>Impl …`/`<name>Spec xs`
calls (in scope over `xs`); `innerTy` is the bare `IRContext …` (the `Option`'s element type).
-/
private meta def mkOptionIRContextMatchBody (declName : Name) (us : List Level) (xs : Array Expr)
    (innerTy implBody specBody : Expr) : Lean.Elab.TermElabM Expr := do
  -- Splice the impl-call discriminant and the spec call in as *pre-built `Expr`s* via `exprToSyntax`
  -- (a syntax leaf that re-elaborates to exactly that expr), NOT via delaboration: `implBody`/`specBody`
  -- mention erased proof projections (e.g. `ctx.sim`) that a delaborate→re-elaborate roundtrip would turn
  -- into fresh *unassigned* metavariables, which then leak into the base def (`declaration has
  -- metavariables`). The `<name>_impl` lemma still goes through delaboration so its `:= by grind`
  -- autoParam args stay pinned.
  let implStx ← Lean.Elab.Term.exprToSyntax implBody
  let specStx ← Lean.Elab.Term.exprToSyntax specBody
  let implLemmaApp := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let implLemmaTerm ← Lean.PrettyPrinter.delab implLemmaApp
  let simCall := mkAppN (mkConst declName us) xs
  let simTerm ← Lean.PrettyPrinter.delab simCall
  let ctorId := mkIdent ``Veir.Sim.IRContext.mk
  let specId := mkIdent (mkSpecName declName)
  let getId := mkIdent ``Option.specGet!
  -- The `sim` proof for the `some buf` branch (cf. `Sim.OperationPtr.setParentWithCheck!`).
  let simProof ← `(term| (by
    have := $implLemmaTerm:term
    have := ($simTerm:term).specGet!.sim
    cases _ : $simTerm:term <;> grind [$specId:ident, $getId:ident]))
  let bodyStx ← `(term|
    match h : $implStx:term with
    | none => none
    | some buf => some ($ctorId:ident buf ($specStx:term).specGet! $simProof:term))
  -- Elaborate the `match` against the expected `Option (IRContext …)` type so the matcher is generated.
  -- `elabTermEnsuringType` *postpones* the `by` block, leaving unsolved synthetic mvars in the returned
  -- term; we must force them (`synthesizeSyntheticMVars`) and `instantiateMVars` so the base def body is
  -- metavariable-free — otherwise later equation-lemma generation for the base hits a dangling mvar
  -- (`unknown metavariable` panic) and the kernel rejects the def (`declaration has metavariables`).
  let expectedTy ← mkAppM ``Option #[innerTy]
  let body ← Lean.Elab.Term.elabTermEnsuringType bodyStx (some expectedTy)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars body

/--
Combine an impl-projection value `impl` and a spec-projection value `spec` back into the original
split shape described by `simInnerTy` (a `<name>Sim` result without its outer `Option`). It descends
`Prod`/`Sigma` in lockstep on both values and, at each split-type leaf, applies that type's constructor
to the paired impl/spec components — `Sim.OperationPtr.mk impl.i spec.i`, and `Sim.IRContext.mk impl.i
spec.i ⋯` for the three-field `IRContext`. This lets the base wrapper rebuild structured results (e.g.
`Option (Sim.IRContext × Sim.OperationPtr)`) from *calls to* `<name>Impl`/`<name>Spec`, so neither is
unfolded inline — instead of re-projecting `<name>Sim`, which would drag its always-inline body along.
-/
private meta partial def mkBuffedCombine (simInnerTy impl spec : Expr) : MetaM Expr := do
  let ty ← whnf simInnerTy
  if let some #[a, b] := appOf? ``Prod 2 ty then
    let fst ← mkBuffedCombine a (← mkAppM ``Prod.fst #[impl]) (← mkAppM ``Prod.fst #[spec])
    let snd ← mkBuffedCombine b (← mkAppM ``Prod.snd #[impl]) (← mkAppM ``Prod.snd #[spec])
    mkAppM ``Prod.mk #[fst, snd]
  else if let some #[a, β] := appOf? ``Sigma 2 ty then
    -- Dependent pair: keep `Sigma`'s type family `β` explicit (`mkAppM` cannot infer the dependent
    -- motive). The result is the `Sim`-level `Sigma`, so its second component's type is `β` applied to
    -- the *combined* first component.
    let fst ← mkBuffedCombine a (← mkAppM ``Sigma.fst #[impl]) (← mkAppM ``Sigma.fst #[spec])
    let snd ← mkBuffedCombine (β.beta #[fst]) (← mkAppM ``Sigma.snd #[impl]) (← mkAppM ``Sigma.snd #[spec])
    pure (mkAppN (mkConst ``Sigma.mk ty.getAppFn.constLevels!) #[a, β, fst, snd])
  else if ty.getAppFn.constName? == some ``Veir.Sim.IRContext then
    rebuildIRContextWithSorrySim ty impl spec
  else if !isSplitType ty then
    -- Non-split leaf (e.g. `UInt64`): `impl` and `spec` are the same value, so the recombination
    -- just returns the impl. (Discards the redundant `spec` call so the base never invokes it.)
    pure impl
  else
    let some typeName := ty.getAppFn.constName?
      | throwError "@[buffed]: cannot combine impl/spec at type {ty}"
    let some rule := findBuffedSplitRule? typeName
      | throwError "@[buffed]: no split rule registered for {typeName}"
    mkAppM rule.ctorName #[impl, spec]

/--
Build the generated non-suffixed wrapper, combining generated `<name>Impl` and `<name>Spec`. When
`recursive` is set, `<name>Impl`/`<name>Spec` are independent recursive functions (not defeq to
projections of `<name>Sim`); a recursive bare-`IRContext` result has its `sim` proof *proven* from the
`<name>_impl` lemma (`rebuildIRContextWithProvenSim`), while `Option (IRContext …)` results still leave
it as `sorry`. Runs in `TermElabM` so the `sim` proof can be discharged by a tactic.
-/
meta def buildBuffedBase (declName : Name) (recursive : Bool) :
    Lean.Elab.TermElabM (Name × Expr × Expr × List Name) := do
  let info ← getConstInfo declName
  let baseName := mkBaseName declName
  let implName := mkImplName declName
  let specName := mkSpecName declName
  let us := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun xs _ => do
    let call := mkAppN (mkConst declName us) xs
    let callTy ← whnf (← inferType call)
    let implArgs ← mkImplArgsFrom xs
    let implBody := mkAppN (mkConst implName us) implArgs
    let specBody := mkAppN (mkConst specName us) xs
    -- `Option (split type)` and `Option (IRContext …)` share one shape: drive the `some`/`none` off
    -- `<name>Impl` and recover the spec component from `<name>Spec` only in the `some` branch, i.e.
    --   `<name>Impl args |>.map (fun x => ⟨x, (<name>Spec args).get sorry⟩)`.
    -- This keeps `<name>Spec` an out-of-line call (never inlined into the impl) while staying
    -- definitionally equal to `<name>Sim`. `rebuild` says how to assemble one `some` element.
    let mapSomeOverImpl (rebuild : Expr → Expr → MetaM Expr) : MetaM Expr := do
      let innerImplTy := (← whnf (← inferType implBody)).getAppArgs[0]!
      let specGet ← mkOptionGetSorry specBody
      let mapFn ← withLocalDeclD `_x innerImplTy fun x => do
        mkLambdaFVars #[x] (← rebuild x specGet)
      mkAppM ``Option.map #[mapFn, implBody]
    let baseBody ←
      match ← classifyReturn callTy with
      | .irContext =>
        if recursive then
          -- For a recursive def `<name>Impl`/`<name>Spec` are independent functions, no longer defeq
          -- to projections of `<name>Sim`. We prove the `sim` proof relating them from the `<name>_impl`
          -- lemma (which must already be emitted) — see `rebuildIRContextWithProvenSim`.
          rebuildIRContextWithProvenSim declName us xs callTy implBody specBody
        else
          let simProof := mkProj ``Veir.Sim.IRContext 2 call
          mkAppM ``Veir.Sim.IRContext.mk #[implBody, specBody, simProof]
      | .bareSplit rule =>
        -- Assemble from calls to the generated `<name>Impl`/`<name>Spec` so the base actually
        -- *invokes* `<name>Spec` (preserving its `@[noinline]`/`@[nospecialize]`) instead of
        -- re-projecting `call`, which would unfold the spec body inline.
        mkAppM rule.ctorName #[implBody, specBody]
      | .optionSplit rule =>
        mapSomeOverImpl fun x specGet => mkAppM rule.ctorName #[x, specGet]
      | .optionIRContext innerTy =>
        if recursive then
          -- A recursive Option-`IRContext` def: `<name>Impl` is an independent recursive function, and
          -- the `_def`/`_impl` lemmas go through `fun_induction`. The `match`-with-proven-`sim` wrapper
          -- (below) is incompatible with that `fun_induction <;> grind [<base>]` recipe, so we keep the
          -- plain `Option.map` with a `sorry` `sim` (`rebuildIRContextWithSorrySim`) here.
          mapSomeOverImpl fun x specGet => rebuildIRContextWithSorrySim innerTy x specGet
        else
          -- Non-recursive: build the body as `match h : <name>Impl … with | none => none | some buf =>
          -- some ⟨buf, (<name>Spec …).specGet!, <proof-using-h>⟩`, *proving* the `sim` field from the
          -- `<name>_impl` lemma (cf. the hand-written `Sim.OperationPtr.setParentWithCheck!`). The
          -- `match` replaces the older `<name>Impl …|>.attach.map fun x => ⟨x.val, …⟩` shape — it keeps
          -- the `sim`-membership fact (now the match equation `h`) without the `Subtype`-projection-over-
          -- erased-`attach`-wrapper pattern. See `mkOptionIRContextMatchBody`.
          mkOptionIRContextMatchBody declName us xs innerTy implBody specBody
      | .other =>
        -- Remaining product / dependent-`Sigma` returns (possibly under `Option`). Rebuild from
        -- *calls to* `<name>Impl`/`<name>Spec` (combined component-wise into the split shape) so the
        -- base invokes them out of line, instead of re-projecting the always-inline `<name>Sim`.
        if let some #[innerSimTy] := appOf? ``Option 1 callTy then
          mapSomeOverImpl fun x specGet => mkBuffedCombine innerSimTy x specGet
        else
          mkBuffedCombine callTy implBody specBody
    let baseTy ← inferType baseBody
    let baseForall ← mkForallFVars xs baseTy
    let baseLambda ← mkLambdaFVars xs baseBody
    pure (baseName, baseForall, baseLambda, info.levelParams)

/-- How `<name>_def` (`<base> args = <name>Sim args`) is proved for return shape `shape`. -/
private inductive DefLemmaProof where
  /-- The base wrapper is *definitionally equal* to `funcSim`, so `Eq.refl` discharges it. The bare
  `.bareSplit`/`.irContext` wrappers are built as `Ctor.mk (proj₀ call) (proj₁ call) …`, which is defeq
  to `call` by structure eta. -/
  | rfl
  /-- An `Option`-returning base wrapper. It reassembles the result via `Option.map`/`sorry`, so it is
  *not* defeq to `funcSim`; instead the lemma is proved by unfolding both sides (`simp [<base>,
  <name>Sim]`) and calling `grind`, mirroring the hand-written `…Sim_def` lemmas. -/
  | optionTactic
  /-- An `Option (IRContext …)`-returning base wrapper, reassembled via `match h : <name>Impl … with …`
  with a *proven* `sim` field (`mkOptionIRContextMatchBody`). The dependent match defeats the plain
  `optionTactic` recipe, so the lemma is proved with the template `split <;> cases … <;> simp_all`
  (mirroring the hand-written `Sim.OperationPtr.setParentWithCheck!_def`). -/
  | optionIRContextTactic
  /-- The `Prod`/`Sigma` (`.other`) base wrapper is reassembled component-wise (`mkBuffedCombine`), so
  it is *not* defeq to `funcSim`. The lemma is proved by unfolding only the `Sim` side (`simp only
  [<name>Sim]`) and calling `grind`. -/
  | otherTactic

/-- How to prove the `<name>_def` lemma for return shape `shape` (see `DefLemmaProof`). -/
private meta def defLemmaProofFor : BaseReturnShape → DefLemmaProof
  | .irContext | .bareSplit _ => .rfl
  | .optionSplit _ => .optionTactic
  | .optionIRContext _ => .optionIRContextTactic
  | .other => .otherTactic

/--
Build the proof term for an `Option`-returning `<name>_def` lemma. `us`/`xs` are the level params and
telescoped parameters (in scope); `instGoalTy` is the *instantiated* equation `<base> xs = <name>Sim xs`
(not the outer `∀`). The base wrapper reassembles the result via `Option.map` from a call to
`<name>Impl`, so unfolding it and rewriting `<name>Impl` back to the `<name>Sim` projection via the
generated `<name>_impl` lemma turns both sides into the same `Option.map` of `<name>Sim`, which `rfl`
closes (cf. `Rewriter.insertOp?_def_example`):

    unfold <base>; rw [← (<name>_impl xs)]; rfl

Crucially we rewrite with the `_impl` lemma **applied to the explicit telescope arguments** `xs`
(delaborated to a term), *not* the bare lemma name: a bare `rw [← <name>_impl]` would leave the lemma's
`:= by grind` autoParam binders as metavariables to be re-synthesized, embedding `autoParam`/grind
goals into the resulting proof term (which then poisons `grind` at downstream call sites). Pinning the
arguments avoids that. Requires the `<name>_impl` lemma to have been emitted (and proven) already.

If the template fails (e.g. `rw` cannot find the pattern, or `rfl` does not close), it falls back to the
older unfold-both-sides recipe `simp only [<base>, <name>Sim]; grind`, mirroring the hand-written
`…Sim_def` lemmas. A `hard error` is raised only if *both* recipes fail.
-/
private meta def mkOptionDefLemmaProof (declName baseName : Name) (us : List Level) (xs : Array Expr)
    (instGoalTy : Expr) : Lean.Elab.TermElabM Expr := do
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  -- `<name>_impl` applied to the explicit telescope args, delaborated to a term for `rw [← …]`.
  let implLemmaApp := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let implTerm ← Lean.PrettyPrinter.delab implLemmaApp
  -- Template (line 64): unfold the base, rewrite `<name>Impl` back via `← (<name>_impl xs)`, close by `rfl`.
  let templateTac ← `(tactic| (unfold $baseId:ident; rw [← $implTerm:term] <;> rfl))
  let attempt : Lean.Elab.TermElabM (Option Expr) := do
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar instGoalTy
    let remaining ← Lean.Elab.Tactic.run goalMVar.mvarId! (Lean.Elab.Tactic.evalTactic templateTac)
    if remaining.isEmpty then pure (some (← instantiateMVars goalMVar)) else pure none
  match ← (try attempt catch _ => pure none) with
  | some proof => pure proof
  | none =>
    -- Fallback: unfold both sides then `grind` (raises a hard error if this also fails).
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar instGoalTy
    let tac ← `(tactic| (simp only [$baseId:ident, $declId:ident]; grind))
    Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
    instantiateMVars goalMVar

/--
Build the proof term for an `Option (IRContext …)`-returning `<name>_def` lemma. `us`/`xs` are the
level params and telescoped parameters (in scope); `instGoalTy` is the *instantiated* equation
`<base> xs = <name>Sim xs`. This base wrapper reassembles the result via `match h : <name>Impl … with …`
with a *proven* `sim` field (`mkOptionIRContextMatchBody`), so the plain `optionTactic` recipe
(`rw [← <name>_impl]; rfl`) does not apply: the dependent `sim` proof field (and the match's own
dependent equation) block both `rfl` and any `rw`/`generalize` on the match discriminant
("motive not type correct"). We first reduce the `Option (IRContext …)` equality to its `buf`/`spec`
projections with `Sim.IRContext.option_ext` (which discards the `sim` field by proof irrelevance),
unfold the base, then `split` the match and `cases` `<name>Sim xs`, closing with `simp_all` (given
`<name>_impl xs`, `<name>Spec`, and `Option.specGet!`), mirroring the hand-written
`Sim.OperationPtr.setAttributes_def_EXAMPLE`:

    apply Sim.IRContext.option_ext
    unfold <base>
    have := <name>_impl xs
    split <;> cases _ : <name>Sim xs <;> simp_all [<name>Spec, Option.specGet!]

`Sim.IRContext.option_ext` turns the goal into `… .map (·.spec) = … ∧ … .map (·.buf) = …`; `split`
exposes the match's `none`/`some buf` branches with the equation `<name>Impl … = none`/`= some buf` as
a plain hypothesis; `cases <name>Sim xs` concretizes the Sim result; and `<name>_impl xs` (relating
`<name>Impl …` to `Option.map (·.buf) (<name>Sim xs)`) lets `simp_all` close every branch. If it fails
it falls back to the unfold-both recipe `simp only [<base>, <name>Sim]; grind` (a hard error if that
also fails). Requires the `<name>_impl` lemma to have been emitted (and proven) already.
-/
private meta def mkOptionIRContextDefLemmaProof (declName baseName : Name) (us : List Level)
    (xs : Array Expr) (instGoalTy : Expr) : Lean.Elab.TermElabM Expr := do
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let specId := mkIdent (mkSpecName declName)
  let getId := mkIdent ``Option.specGet!
  -- `<name>_impl` applied to the explicit telescope args, delaborated to a term so the autoParam args
  -- are pinned (a bare `<name>_impl` would re-synthesize its `:= by grind` autoParams).
  let implLemmaApp := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let implTerm ← Lean.PrettyPrinter.delab implLemmaApp
  -- Template: strip the `sim` field via `option_ext`, unfold the base, add `<name>_impl xs` as a fact,
  -- then `split` the match and close each branch with `simp_all [<name>Spec, Option.specGet!]` (which
  -- chains `<name>_impl` with the branch equation `<name>Impl … = none`/`= some buf` and case-splits
  -- `<name>Sim xs` via `Option.map_eq_none`/`_some`) finishing with `grind` (cf. the hand-written
  -- `Sim.OperationPtr.setAttributes_def_EXAMPLE`). We *don't* `cases <name>Sim xs`: it destructures its
  -- args (e.g. `match _ : ctx`), so an explicit `cases` yields a type-incorrect motive.
  let templateTac ← `(tactic|
    (apply Veir.Sim.IRContext.option_ext
     unfold $baseId:ident
     have := $implTerm:term
     split <;> simp_all [$specId:ident, $getId:ident] <;> grind))
  let attempt : Lean.Elab.TermElabM (Option Expr) := do
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar instGoalTy
    let remaining ← Lean.Elab.Tactic.run goalMVar.mvarId! (Lean.Elab.Tactic.evalTactic templateTac)
    if remaining.isEmpty then pure (some (← instantiateMVars goalMVar)) else pure none
  match ← (try attempt catch _ => pure none) with
  | some proof => pure proof
  | none =>
    -- Fallback: unfold both sides then `grind` (raises a hard error if this also fails).
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar instGoalTy
    let tac ← `(tactic| (simp only [$baseId:ident, $declId:ident]; grind))
    Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
    instantiateMVars goalMVar

/--
Build the proof term for a `Prod`/`Sigma` (`.other`) `<name>_def` lemma of type `goalTy` (the full
`∀ xs, <base> xs = <name>Sim xs`). The base wrapper recombines components rather than projecting
`<name>Sim`, so it is not defeq; we unfold both sides and let `grind` finish:

    intros; simp only [<baseName>, <declName>]; grind

A `hard error` (no `sorry`, no skipping) is raised if the tactic block fails, so a `buffed` def whose
`_def` lemma cannot be proved this way fails loudly.
-/
private meta def mkOtherDefLemmaProof (baseName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let tac ← `(tactic| (intros; simp only [$baseId:ident, $declId:ident]; grind))
  Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
  instantiateMVars goalMVar

/--
Build the proof term for a *recursive* `<name>_def` lemma of type `goalTy` (the full
`∀ xs, <base> xs = <name>Sim xs`). For a recursive def `<base>`/`<name>Impl` are independent recursive
functions (not defeq to projections of `<name>Sim`), so we prove the equation by induction along
`<name>Sim`'s own recursion, mirroring the hand-written `…Sim_def` lemmas:

    fun_induction <name>Sim <;> grind [<base>]

The leading `intros` brings the parameters into context so `fun_induction` can find the call of
`<name>Sim` in the (now quantifier-free) goal. A `hard error` (no `sorry`, no skipping) is raised if the
tactic block fails, so a recursive `buffed` def whose `_def` lemma cannot be proved this way fails loudly.
-/
private meta def mkRecursiveDefLemmaProof (baseName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let tac ← `(tactic| (intros; fun_induction $declId:ident <;> grind (gen := 20) [$baseId:ident]))
  Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
  instantiateMVars goalMVar

/--
Build the proof term for a recursive *bare-`IRContext`* `<name>_def` lemma of type `goalTy`
(`∀ xs, <base> xs = <name>Sim xs`). Here the base carries a *proven* `sim` field referencing
`<name>Sim` (`rebuildIRContextWithProvenSim`), which defeats the `fun_induction <;> grind [<base>]`
recipe. Instead we unfold the base and `<name>Spec` to expose `⟨<name>Impl …, <name>Spec …, _⟩`, rewrite
the `buf` back to `(<name>Sim …).buf` via `<name>_impl`, and close by `rfl` (structure eta + proof
irrelevance on `sim`):

    unfold <base> <name>Spec; rw [← <name>_impl]; rfl
-/
private meta def mkRecursiveIRContextDefLemmaProof (baseName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let baseId := mkIdent baseName
  let specId := mkIdent (mkSpecName declName)
  let implId := mkIdent (mkImplLemmaName declName)
  -- `simp only` (rather than `rw`) handles the dependent rewrite under the `sim` proof field; after
  -- unfolding the base and `<name>Spec` and rewriting `buf` back via `← <name>_impl`, the goal closes.
  let tac ← `(tactic|
    (intros; simp only [$baseId:ident, $specId:ident, ← $implId:ident]))
  Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
  instantiateMVars goalMVar

/--
Build the proof term for a *recursive* `<name>_impl` lemma of type `goalTy` (the full
`∀ xs, (funcSim args).impl = funcImpl (projected args)`). For a recursive def `<name>Impl` is an
independent recursive function, so we prove the equation by induction along `<name>Sim`'s own
recursion, unfolding `<name>Impl` in each case and closing with `grind` (given the `Sim.*Ptr` split
structures as hints), mirroring the hand-written `…_impl` lemmas (e.g.
`Rewriter.replaceValue?_impl_example`):

    fun_induction <name>Sim <;>
    · unfold <name>Impl
      grind (instances := 2000) [Sim.IRContext, Sim.OperationPtr, …]

The leading `intros` brings the parameters into context so `fun_induction` can find the call of
`<name>Sim` in the (now quantifier-free) goal. The `grind` hints are the split structures from
`buffedSplitTable` (every `Sim.*Ptr` plus `Sim.IRContext`), so `grind` can reason about their
projections/eta. Unlike the older `lift_lets; intros; repeat (…)` recipe (tailored to the bare
`IRContext` shape), this closes `Option`-returning recursions too (e.g. `replaceValue?`).
If the tactic block fails the proof emits a warning and falls back to `sorry`, so `buffed` never breaks
the build — the `_impl` lemma is still emitted, just left unproven.
-/
private meta def mkRecursiveImplLemmaProof (implName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let implId := mkIdent implName
  let declId := mkIdent declName
  -- `grind` hints: the split structures from `buffedSplitTable` (`Sim.IRContext` + every `Sim.*Ptr`),
  -- so `grind` reasons about their projections/eta when relating `<name>Sim` to `<name>Impl`.
  let grindHints ← (#[``Veir.Sim.IRContext] ++ buffedSplitTable.map (·.typeName)).mapM
    fun n => `(Lean.Parser.Tactic.grindParam| $(mkIdent n):ident)
  let tac ← `(tactic| (intros; fun_induction $declId:ident <;>
    (unfold $implId:ident
     grind (instances := 2000) [$grindHints,*])))
  -- Run the tactic with `Tactic.run`, which returns the *remaining* goals rather than logging an
  -- `unsolved goals` error. If the block either throws or leaves goals open, the template proof does
  -- not apply to this shape, so we fall back to a `sorry` placeholder (and `buffed` keeps building).
  --
  -- A failing closing `grind` *logs* an error into the message log (besides leaving goals open), which
  -- would fail the surrounding command even though we recover. So we snapshot the message log up front
  -- and restore it on the failure path, discarding any diagnostics emitted by the failed attempt.
  let savedLog := (← getThe Core.State).messages
  let attempt : Lean.Elab.TermElabM (Option Expr) := do
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
    let remaining ← Lean.Elab.Tactic.run goalMVar.mvarId! (Lean.Elab.Tactic.evalTactic tac)
    if remaining.isEmpty then
      pure (some (← instantiateMVars goalMVar))
    else
      pure none
  match ← (try attempt catch _ => pure none) with
  | some proof => pure proof
  | none =>
    -- Drop any error/diagnostic messages the failed attempt logged, then warn and fall back to `sorry`.
    modifyThe Core.State (fun s => { s with messages := savedLog })
    logWarning m!"@[buffed]: could not prove the `_impl` lemma {implName} (recursive) for {declName}; \
      falling back to `sorry`"
    mkSorry goalTy (synthetic := false)

/--
Build the `<name>_def` lemma `<base> args = <name>Sim args`, relating the generated base wrapper back to
the original Sim-level definition (e.g. `getFirstUse ctx ptr ib = getFirstUseSim ctx ptr ib`).

For a *non-recursive* def (`recursive := false`), the base is built by projecting `<name>Sim`, so the
bare `.irContext`/`.bareSplit` shapes are defeq and proved by `Eq.refl`; `Option`-returning shapes are
not defeq and proved by `simp [<base>, <name>Sim]; grind` (see `mkOptionDefLemmaProof`); and the
`Prod`/`Sigma` (`.other`) shape is proved by `simp only [<name>Sim]; grind` (see `mkOtherDefLemmaProof`).

For a *recursive* def (`recursive := true`), `<base>`/`<name>Impl` are independent recursive functions
(not defeq to projections of `<name>Sim`), so *every* return shape is proved by induction along
`<name>Sim` — `fun_induction <name>Sim <;> grind [<base>]` (see `mkRecursiveDefLemmaProof`), matching
the hand-written `…Sim_def` lemmas (e.g. `Rewriter.detachOperands.loop_def`). The recursive
`Prod`/`Sigma` (`.other`) shape returns `none` (no `_def` lemma), since `fun_induction` is unreliable there.
-/
meta def buildBuffedDefLemma (declName : Name) (recursive : Bool) :
    Lean.Elab.TermElabM (Option (Name × Expr × Expr × List Name)) := do
  let info ← getConstInfo declName
  let defName := mkDefName declName
  let baseName := mkBaseName declName
  let us := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun xs _ => do
    let simCall := mkAppN (mkConst declName us) xs
    let callTy ← whnf (← inferType simCall)
    let shape ← classifyReturn callTy
    let baseCall := mkAppN (mkConst baseName us) xs
    let eqTy ← mkEq baseCall simCall
    let defForall ← mkForallFVars xs eqTy
    if recursive then
      -- Recursive: base is an independent recursive function, so prove the equation by `fun_induction`
      -- (the defeq `rfl` proof no longer applies). The `Prod`/`Sigma` (`.other`) shape is skipped here,
      -- since `fun_induction` does not reliably close it.
      if let .other := shape then return none
      -- A bare-`IRContext` base now carries a *proven* `sim` field referencing `<name>Sim`, which
      -- defeats `fun_induction <;> grind [<base>]`; use the unfold-and-rewrite recipe instead.
      let defProof ←
        if let .irContext := shape then
          mkRecursiveIRContextDefLemmaProof baseName declName defForall
        else
          mkRecursiveDefLemmaProof baseName declName defForall
      return some (defName, defForall, defProof, info.levelParams)
    match defLemmaProofFor shape with
    | .rfl =>
      -- The two sides are defeq (structure eta), so `Eq.refl` discharges it.
      let defProof ← mkLambdaFVars xs (← mkEqRefl baseCall)
      return some (defName, defForall, defProof, info.levelParams)
    | .optionTactic =>
      -- Prove the *instantiated* goal `eqTy` with `xs` in scope (so the `_impl` lemma can be applied to
      -- the explicit args), then abstract the parameters back out.
      let instProof ← mkOptionDefLemmaProof declName baseName us xs eqTy
      let defProof ← mkLambdaFVars xs instProof
      return some (defName, defForall, defProof, info.levelParams)
    | .optionIRContextTactic =>
      -- The `Option (IRContext …)` base uses `match h : <name>Impl … with …` with a proven `sim`; the
      -- dependent match blocks the plain `optionTactic` `rfl`, so use the `split <;> cases … <;>
      -- simp_all` recipe.
      let instProof ← mkOptionIRContextDefLemmaProof declName baseName us xs eqTy
      let defProof ← mkLambdaFVars xs instProof
      return some (defName, defForall, defProof, info.levelParams)
    | .otherTactic =>
      let defProof ← mkOtherDefLemmaProof baseName declName defForall
      return some (defName, defForall, defProof, info.levelParams)

/--
Build the proof term for a *non-recursive* `Option`-returning `<name>_impl` lemma of type `goalTy` (the
full `∀ xs, Option.map (·.buf) (<name>Sim xs) = <name>Impl (projected xs)`). `<name>Impl` is *defined* as
this `Option.map` projection of `<name>Sim`, so unfolding it exposes the projection and `grind` finishes,
mirroring the hand-written `…_impl` lemmas (e.g. `Rewriter.insertOp?_impl_example`):

    intros; unfold <name>Impl; grind

`unfold <name>Impl` only names the head constant (it does not re-elaborate the call's arguments, so no
`:= by grind` autoParam default is synthesized). If the tactic block throws or leaves goals open, it
emits a warning and falls back to `sorry`, so `buffed` never breaks the build — the `_impl` lemma is
still emitted, just left unproven.
-/
private meta def mkOptionImplLemmaProof (implName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let implId := mkIdent implName
  let tac ← `(tactic| (intros; unfold $implId:ident; grind))
  let attempt : Lean.Elab.TermElabM (Option Expr) := do
    let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
    let remaining ← Lean.Elab.Tactic.run goalMVar.mvarId! (Lean.Elab.Tactic.evalTactic tac)
    if remaining.isEmpty then
      pure (some (← instantiateMVars goalMVar))
    else
      pure none
  match ← (try attempt catch _ => pure none) with
  | some proof => pure proof
  | none =>
    logWarning m!"@[buffed]: could not prove the `_impl` lemma {implName}; falling back to `sorry`"
    mkSorry goalTy (synthetic := false)

/--
Build the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)`, relating the impl
projection of the original `Sim`-level result to a call of the generated `<name>Impl` on the flattened
(impl/spec-split) arguments — the same projection `buildBuffedImpl` performs to *define* `<name>Impl`.

The LHS is `mkBuffedProj 0 (funcSim args)` (the result's field-0 projection: `.buf` for `IRContext`,
`.impl`/`Option.map`/… for other shapes) and the RHS is `<name>Impl (mkImplArgsFrom args)`.

For a *recursive* def the proof is built by induction along `<name>Sim`, unfolding `<name>Impl` in each
case (see `mkRecursiveImplLemmaProof`), mirroring the hand-written `…_impl` lemmas. For a
*non-recursive* `Option`-returning def the proof is `unfold <name>Impl; grind` (see
`mkOptionImplLemmaProof`), since `<name>Impl` is *defined* as the `Option.map` projection of
`<name>Sim`. Every other non-recursive shape (`irContext`, `bareSplit`, `Prod`/`Sigma`) defines
`<name>Impl` as the field-0 projection of `<name>Sim`, so the two sides are defeq and the proof is
`Eq.refl` (cf. the hand-written `Rewriter.pushOperandAt_impl_exmaple := by rfl`).
-/
meta def buildBuffedImplLemma (declName : Name) (recursive : Bool) :
    Lean.Elab.TermElabM (Name × Expr × Expr × List Name) := do
  let info ← getConstInfo declName
  let implLemmaName := mkImplLemmaName declName
  let implName := mkImplName declName
  let us := info.levelParams.map Level.param
  forallTelescopeReducing info.type fun xs _ => do
    let simCall := mkAppN (mkConst declName us) xs
    let callTy ← whnf (← inferType simCall)
    let shape ← classifyReturn callTy
    -- LHS: the impl (field-0) projection of the Sim result, exactly as `buildBuffedImpl` builds it.
    -- `named := true` so the statement reads `(funcSim …).buf`/`.impl` rather than `.1`.
    let lhs ← mkBuffedProj 0 simCall (named := true)
    -- RHS: `<name>Impl` applied to the flattened impl/spec-split arguments, projected by name (`ctx.buf`,
    -- `ptr.impl`, …) rather than by index.
    let implArgs ← mkImplArgsFrom xs (named := true)
    let rhs := mkAppN (mkConst implName us) implArgs
    let eqTy ← mkEq lhs rhs
    let implForall ← mkForallFVars xs eqTy
    let proof ←
      if recursive then
        mkRecursiveImplLemmaProof implName declName implForall
      else
        -- `Option`-returning shapes get the `unfold <name>Impl; grind` template proof. Every other
        -- non-recursive shape (`irContext`, `bareSplit`, `Prod`/`Sigma`) defines `<name>Impl` as the
        -- field-0 projection of `<name>Sim` (`buildBuffedImpl`), so the LHS `(funcSim …).buf`/`.impl`
        -- and the RHS `<name>Impl (projected …)` are *definitionally equal* and `Eq.refl` discharges
        -- the lemma (cf. the hand-written `Rewriter.pushOperandAt_impl_exmaple := by rfl`).
        match shape with
        | .optionSplit _ | .optionIRContext _ => mkOptionImplLemmaProof implName implForall
        | _ => mkLambdaFVars xs (← mkEqRefl lhs)
    pure (implLemmaName, implForall, proof, info.levelParams)

end Veir.Buffed

/--
Apply a bare attribute `@[<attrName>]` to an already-added declaration through the standard attribute
machinery, exactly as if it were written `@[<attrName>]` in source. We build the `Attr.simple` syntax
the parser produces for a no-argument attribute and feed it to `Attribute.add`, mirroring the
`@[inline]` syntax emitted for the recursive `<name>Impl`. The declaration must already exist in the
environment.
-/
private meta def applyBareAttr (name attrName : Name) : AttrM Unit := do
  let stx := Syntax.node .none ``Lean.Parser.Attr.simple #[mkIdent attrName, Syntax.node .none nullKind #[]]
  Attribute.add name attrName stx (kind := .global)

/--
Set the inline attribute for an already-added declaration through the `@[inline]`/`@[noinline]`
attribute syntax (the same path the recursive `<name>Impl` uses).
-/
private meta def setInlineAttr (name : Name) (inline? : Bool := true) : AttrM Unit := do
  trace[Buffed.ghosting] "Setting inline attribute for {name} to {inline?}"
  if inline? then
    applyBareAttr name `inline
  else
    applyBareAttr name `noinline

/--
Add a generated declaration `(name, type, value, levelParams)`, tag its inline attribute, then
compile it.

We split the usual `addAndCompile` into `addDecl` → `setInlineAttr` → `compileDecl` so the inline
flag is in the environment *before* code generation runs. The compiler bakes the inline flag into the
base-phase LCNF decl (and thus into the reduce-arity wrapper `<name>._redArg` it later splits off);
tagging *after* compilation is too late, leaving `<name>._redArg` out-of-line so that callers route
through it instead of inlining the wrapper.
-/
private meta def addBuffedDecl (name : Name) (type value : Expr) (levelParams : List Name)
    (inline? : Bool) (nospecialize? : Bool := false) : AttrM Unit := do
  let decl : Declaration := .defnDecl {
    name, levelParams, type, value
    hints := .regular 0
    safety := .safe
  }
  addDecl decl
  setInlineAttr name (inline? := inline?)
  if nospecialize? then
    applyBareAttr name `nospecialize
  compileDecl decl

/-- Add a generated theorem `(name, type, value, levelParams)`. Unlike `addBuffedDecl`, a theorem is
proof-irrelevant data, so it is neither tagged with an inline attribute nor compiled. -/
private meta def addBuffedThm (name : Name) (type value : Expr) (levelParams : List Name) : AttrM Unit := do
  addDecl <| .thmDecl { name, levelParams, type, value }

/--
Emit the `<name>_def` lemma relating the base wrapper to `funcSim` (e.g.
`getFirstUse ctx ptr ib = getFirstUseSim ctx ptr ib`), unless it already exists or the return shape is
one for which no `_def` is emitted (`Prod`/`Sigma`). The `recursive` flag selects the proof recipe:
non-recursive shapes are defeq (`rfl`) or `simp; grind`; recursive ones use `fun_induction` (see
`buildBuffedDefLemma`). Shared by the recursive and non-recursive `buffed` paths.
-/
private meta def generateBuffedDefLemma (decl : Name) (recursive : Bool) : AttrM Unit := do
  let defName := Veir.Buffed.mkDefName decl
  unless (← getEnv).contains defName do
    if let some (defName, defType, defValue, defLevelParams) ←
        MetaM.run' (Veir.Buffed.buildBuffedDefLemma decl recursive).run' then
      trace[Buffed.ghosting] "Generating {defName} for {decl}"
      addBuffedThm defName defType defValue defLevelParams

/--
Emit the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)` (see
`buildBuffedImplLemma`), unless it already exists. Shared by the recursive and non-recursive `buffed`
paths: recursive defs get a `fun_induction` proof, non-recursive ones a `sorry` placeholder.
-/
private meta def generateBuffedImplLemma (decl : Name) (recursive : Bool) : AttrM Unit := do
  let implLemmaName := Veir.Buffed.mkImplLemmaName decl
  unless (← getEnv).contains implLemmaName do
    let (implLemmaName, implType, implValue, implLevelParams) ←
      MetaM.run' (Veir.Buffed.buildBuffedImplLemma decl recursive).run'
    trace[Buffed.ghosting] "Generating {implLemmaName} for {decl}"
    addBuffedThm implLemmaName implType implValue implLevelParams

/--
Generate the `<name>Spec` ghost projection and the non-suffixed base wrapper from `funcSim`. Both are
unconditionally derived from the elaborated `funcSim` term (`buildBuffedSpec`/`buildBuffedBase`) and
are unaffected by whether `funcSim` is recursive — only `<name>Impl` differs in the recursive case.
-/
private meta def generateBuffedSpecAndBase (decl : Name) (recursive : Bool) : AttrM Unit := do
  let specName := Veir.Buffed.mkSpecName decl
  unless (← getEnv).contains specName do
    trace[Buffed.ghosting] "Generating {specName} for {decl}"
    let (specName, specType, specValue, specLevelParams) ← MetaM.run' (Veir.Buffed.buildBuffedSpec decl)
    -- The spec is kept out of line (`@[noinline]`) and unspecialized (`@[nospecialize]`) so the impl
    -- never inlines it and no specialized copies of the ghost spec are generated.
    addBuffedDecl specName specType specValue specLevelParams (inline? := false) (nospecialize? := true)
  Lean.enableRealizationsForConst specName
  let baseName := Veir.Buffed.mkBaseName decl
  unless (← getEnv).contains baseName do
    trace[Buffed.ghosting] "Generating {baseName} for {decl}"
    let (baseName, baseType, baseValue, baseLevelParams) ← MetaM.run' (Veir.Buffed.buildBuffedBase decl recursive).run'
    addBuffedDecl baseName baseType baseValue baseLevelParams (inline? := true)
  Lean.enableRealizationsForConst baseName

/--
Generate `<name>Impl`, `<name>Spec`, and the non-suffixed base wrapper from an already-elaborated
Sim-level definition `decl`. This is the *non-recursive* impl path: `<name>Impl` is the field-0
projection of `funcSim` (`buildBuffedImpl`), matching the historical `@[buffed]` attribute. Recursive
defs route `<name>Impl` through `generateBuffedImplRecursive` (in the `buffed` command) instead;
`<name>Spec`/base are identical either way.

`defLemma` controls whether the `<name>_def` lemma is emitted (the `(def_lemma := …)` flag).
-/
meta def generateBuffed (decl : Name) (inline : Bool) (defLemma : Bool := true) : AttrM Unit := do
  Veir.Buffed.checkSim decl
  let implName := Veir.Buffed.mkImplName decl
  unless (← getEnv).contains implName do
    trace[Buffed.ghosting] "Generating {implName} for {decl}"
    let (implName, implType, implValue, levelParams) ← MetaM.run' (Veir.Buffed.buildBuffedImpl decl)
    addBuffedDecl implName implType implValue levelParams (inline? := inline)
  Lean.enableRealizationsForConst implName
  -- Emit the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)`. Non-recursive: the
  -- two sides are defeq but the proof is left as `sorry` for now.
  generateBuffedImplLemma decl (recursive := false)
  generateBuffedSpecAndBase decl (recursive := false)
  -- Emit the `<name>_def` lemma relating the base wrapper to `funcSim` (e.g.
  -- `getFirstUse ctx ptr ib = getFirstUseSim ctx ptr ib`). Defeq shapes get a `rfl` proof; the
  -- `Option`-returning shapes a `simp [<base>, <name>Sim]; grind` proof.
  if defLemma then
    generateBuffedDefLemma decl (recursive := false)

/-! ## Recursive `<name>Impl` generation

For a *recursive* `funcSim`, the field-0 projection of `funcSim` (the non-recursive impl path) would
keep the recursion running inside `funcSim` — dragging the ghost spec and `sorry` proofs through every
iteration. Instead we re-emit a genuinely recursive `def funcImpl` whose self-calls go to `funcImpl`,
and let Lean's equation compiler handle structural recursion and `termination_by`.

The impl *signature* is reused from `buildBuffedImpl` (delaborated to syntax); only the *body* is
rewritten from `funcSim`'s source with three edits (see `rewriteImplBody`). `funcSpec`/base are
unchanged. -/

namespace Veir.Buffed

open Lean Elab Command Term PrettyPrinter

/-- Per source parameter: how it maps to impl parameters and how to project it in the body. -/
private structure ParamPlan where
  /-- The user-facing name of the original `funcSim` parameter (e.g. `ctx`). -/
  userName : Name
  /-- For a split parameter, the structure's field accessor names (`#[buf, spec, sim]`); empty when
  the parameter passes through unchanged. -/
  fieldAccessors : Array Name := #[]
  /-- For a split parameter, the generated impl field-parameter names (`#[ctx_buf, GHOST_ctx_spec,
  ctx_sim]`), in field order. -/
  implFieldNames : Array Name := #[]
  /-- For a split parameter, its structure type as syntax (e.g. `Sim.IRContext OpInfo`), used to
  ascribe the rebinding `let`. -/
  structType? : Option Term := none
  /-- For a split parameter, the structure's constructor (e.g. `Sim.IRContext.mk`), used to spell the
  reconstructed value `Sim.IRContext.mk ctx_buf GHOST_ctx_spec ctx_sim` in delaborated proof types. -/
  ctorName? : Option Name := none
  /-- For a split parameter, each field's type as syntax (`#[IRBufContext OpInfo, IRContext OpInfo,
  Sim ctx_buf GHOST_ctx_spec]`), used as the generated impl field-parameter types. -/
  fieldTypes : Array Term := #[]

/-- Classify each explicit parameter of `funcSim` for the recursive body rewrite. Only *explicit*
parameters are kept, since the self-call in the source provides exactly the explicit arguments
positionally (implicit `OpInfo`/instance arguments are passed implicitly). -/
private meta def buffedParamPlan (declName : Name) : MetaM (Array ParamPlan) := do
  let info ← getConstInfo declName
  -- Delaborate field types with field notation off so dot-receivers like `ctx_sim`'s
  -- `Sim ctx_buf GHOST_ctx_spec` stay applicative and re-parse cleanly.
  forallTelescopeReducing info.type fun xs _ => do
    let mut plans := #[]
    for x in xs do
      let xDecl ← x.fvarId!.getDecl
      unless xDecl.binderInfo.isExplicit do continue
      let xTyWhnf ← whnf xDecl.type
      match xTyWhnf.getAppFn.constName?.bind findBuffedSplitRule? with
      | some rule =>
        let some sInfo := getStructureInfo? (← getEnv) rule.typeName
          | throwError "@[buffed]: expected a structure type for {rule.typeName}"
        let base := xDecl.userName.toString
        let implFieldNames := rule.fieldSuffixes.map fun s =>
          Name.mkSimple <| if s == "spec" then s!"GHOST_{base}_{s}" else s!"{base}_{s}"
        let structType ← delab xTyWhnf
        -- Reconstruct each field's type with the impl field names bound as locals, so dependent
        -- fields (e.g. `sim : Sim ctx_buf GHOST_ctx_spec`) delaborate with the generated names.
        let ctorInfo ← getConstInfo rule.ctorName
        let tyArgs := xTyWhnf.getAppArgs
        let fieldTypes ← forallTelescopeReducing ctorInfo.type fun ctorXs _ => do
          let fieldCount := rule.fieldSuffixes.size
          let paramCount := ctorXs.size - fieldCount
          let ctorParams := ctorXs.extract 0 paramCount
          let ctorFields := ctorXs.extract paramCount ctorXs.size
          let structParams := tyArgs.extract 0 paramCount
          -- Introduce a local named after each impl field, threaded into later field types.
          let rec go (i : Nat) (locals : Array Expr) (acc : Array Term) : MetaM (Array Term) := do
            if h : i < fieldCount then
              let fldTy := (← ctorFields[i]!.fvarId!.getDecl).type.replaceFVars
                (ctorParams ++ ctorFields.extract 0 i) (structParams ++ locals)
              let tyStx ← withOptions (·.setBool `pp.fieldNotation false) <| delab fldTy
              withLocalDeclD implFieldNames[i]! fldTy fun fv => go (i + 1) (locals.push fv) (acc.push tyStx)
            else
              return acc
          go 0 #[] #[]
        plans := plans.push
          { userName := xDecl.userName, fieldAccessors := sInfo.fieldNames, implFieldNames,
            structType? := some structType, ctorName? := rule.ctorName, fieldTypes }
      | none =>
        plans := plans.push { userName := xDecl.userName }
    return plans

/-- The reconstructed-value term for a split parameter: `Sim.IRContext.mk ctx_buf GHOST_ctx_spec ctx_sim`. -/
private meta def ParamPlan.reconstruct (p : ParamPlan) : MacroM (Option Term) := do
  let some ctor := p.ctorName? | return none
  let args := p.implFieldNames.map (mkIdent ·)
  return some (← `($(mkIdent ctor) $args*))

/-- Substitute every split parameter identifier in `stx` with its reconstructed `Ctor.mk …` term, so a
proof type like `ptr.InBounds ctx` becomes `(Sim.OperationPtr.mk ptr_impl …).InBounds (Sim.IRContext.mk …)`.
Dotted identifiers whose *head* component is a split parameter (e.g. `ctx.spec`, `op.InBounds`) are
rewritten through the projection, `(Sim.IRContext.mk …).spec`. -/
private meta partial def substSplitIdents (plans : Array ParamPlan) (stx : Syntax) : MacroM Syntax := do
  if stx.isIdent then
    let id := stx.getId.eraseMacroScopes
    -- Match either the whole ident (`ctx`) or its head component (`ctx` in `ctx.spec`). Hygiene
    -- markers are erased first so a delaborated `blockPtr✝.spec` still matches the `blockPtr` plan.
    let comps := id.components
    if let some head := comps.head? then
      if let some p := plans.find? (fun p => p.userName == head && p.ctorName?.isSome) then
        if let some r ← p.reconstruct then
          -- Re-attach the remaining components as field projections on the reconstructed value.
          let rest := comps.tail.foldl (· ++ ·.eraseMacroScopes) Name.anonymous
          if rest.isAnonymous then return r.raw
          else return (← `($r.$(mkIdent rest):ident)).raw
    return stx
  match stx with
  | .node info kind cs => return .node info kind (← cs.mapM (substSplitIdents plans))
  | _ => return stx

/--
Build the recursive impl's `def` binders + return type. Parameters come from the **source** binders
(`$defn`'s `optDeclSig`), transformed per `plans`: a split-type binder expands into its impl field
binders; other binders keep their source type with split identifiers substituted by `Ctor.mk …`
(so proof types re-elaborate), dropping any `:= by …` autoParam default. The return type is the
field-0-projected impl return, taken from `buildBuffedImpl` (a simple type that delaborates cleanly).
-/
private meta def buffedImplSig (declName : Name) (plans : Array ParamPlan) (defn : Syntax)
    : CommandElabM (Array Syntax × Term) := do
  -- Return type: field-0 projection of the source return (e.g. `Option (IRBufContext OpInfo)`).
  let (_, implType, _, _) ← liftCoreM <| MetaM.run' (Veir.Buffed.buildBuffedImpl declName)
  let retTy ← liftTermElabM <| Meta.forallTelescopeReducing implType fun _ body =>
    PrettyPrinter.delab body
  -- Source binders live in `optDeclSig[0]` as a `null` node of bracketedBinders.
  let srcBinders := defn[2][0].getArgs
  let mut binders : Array Syntax := #[]
  for b in srcBinders do
    if b.isOfKind ``Parser.Term.explicitBinder then
      -- `( <ids> <: type>? <:= default>? )` — names at [1], type at [2][1], default at [3].
      let ids := b[1].getArgs
      let tyStx : Term := ⟨b[2][1]⟩
      let isSplit := fun (idStx : Syntax) =>
        (plans.find? (fun p => p.userName == idStx.getId && p.ctorName?.isSome)).isSome
      if ids.all (! isSplit ·) then
        -- No split names: keep the binder verbatim — including any `:= by …` autoParam default, which
        -- self-calls may rely on — only substituting split identifiers in its type.
        let tyStx' : Term := ⟨← liftMacroM <| substSplitIdents plans tyStx⟩
        binders := binders.push (b.setArg 2 ((b[2]).setArg 1 tyStx'))
      else
        -- A binder may bind several names sharing one type (`(fromOp toOp : T)`); expand split names
        -- to their field binders and group consecutive non-split names. (Split params are never
        -- autoParams, so no default is dropped here.)
        let mut keepIds : Array Syntax := #[]
        let flushKept : Array Syntax → CommandElabM (Array Syntax) := fun kept => do
          if kept.isEmpty then return #[]
          let tyStx' : Term := ⟨← liftMacroM <| substSplitIdents plans tyStx⟩
          let idsStx : TSyntaxArray `ident := kept.map (⟨·⟩)
          return #[(← `(Parser.Term.bracketedBinderF| ($idsStx:ident* : $tyStx'))).raw]
        for idStx in ids do
          match plans.find? (fun p => p.userName == idStx.getId && p.ctorName?.isSome) with
          | some p =>
            binders := binders ++ (← flushKept keepIds); keepIds := #[]
            for (fld, ty) in p.implFieldNames.zip p.fieldTypes do
              -- A field type may mention *another* split parameter (`Sim … [blockPtr.spec]`); rewrite
              -- those references to their reconstructed `Ctor.mk …` form too.
              let ty' : Term := ⟨← liftMacroM <| substSplitIdents plans ty⟩
              binders := binders.push (← `(Parser.Term.bracketedBinderF| ($(mkIdent fld) : $ty'))).raw
          | none => keepIds := keepIds.push idStx
        binders := binders ++ (← flushKept keepIds)
    else
      -- Implicit `{…}` / instance `[…]` binders (e.g. `OpInfo`, `inst`) pass through verbatim.
      binders := binders.push b
  return (binders, retTy)

/-! ### Body rewrite (edits 2 and 3; edit 1 prepends rebinding `let`s) -/

/-- The leftmost head identifier of an application/term, peeling `Term.app` left-spines. -/
private meta partial def headIdent? (stx : Syntax) : Option Name :=
  if stx.isOfKind ``Parser.Term.app then headIdent? stx[0]
  else if stx.isIdent then some stx.getId
  else none

/--
Whether the written identifier `ident` denotes the fully-qualified `name`. The source may write `name`
in a shortened, namespace-relative form (e.g. `Sim.OperationPtr.fooSim` for
`Veir.Sim.OperationPtr.fooSim`), so we accept any trailing-component suffix match.
-/
private meta def identDenotes (name ident : Name) : Bool :=
  name == ident || name.toString.endsWith s!".{ident}"

/-- Whether `stx` is an application (or bare reference) whose head identifier denotes `name`. -/
private meta def isCallOf (name : Name) (stx : Syntax) : Bool :=
  match headIdent? stx with
  | some h => identDenotes name h
  | none => false

/-- Whether the body syntax `stx` contains a (possibly namespace-relative) self-call to `name`. -/
private meta partial def mentionsCall (name : Name) (stx : Syntax) : Bool :=
  if stx.isIdent then identDenotes name stx.getId
  else stx.getArgs.any (mentionsCall name)

/--
Edit 2: rewrite a self-recursive call `funcSim a₁ … aₙ` to `funcImpl (explode a₁) … (explode aₙ)`,
where a split-type argument `aᵢ` is exploded into its field accessors (`ctx ↦ ctx.buf ctx.spec
ctx.sim`). Only the callee name and the split-type positional arguments change; proof args are kept.
-/
private meta partial def rewriteSelfCalls
    (simName implName : Name) (plans : Array ParamPlan) (stx : Syntax) : MacroM Syntax := do
  if stx.isOfKind ``Parser.Term.app && isCallOf simName stx then
    let args := stx[1].getArgs
    let mut newArgs : Array Syntax := #[]
    for i in [0:args.size] do
      let arg := args[i]!
      let accessors : Array Name := (plans[i]?.map (fun p => p.fieldAccessors)).getD #[]
      if accessors.isEmpty then
        newArgs := newArgs.push arg
      else
        for acc in accessors do
          newArgs := newArgs.push (← `($(⟨arg⟩).$(mkIdent acc):ident)).raw
    return ← `($(mkIdent implName) $(newArgs.map (⟨·⟩))*)
  match stx with
  | .node info kind cs => return .node info kind (← cs.mapM (rewriteSelfCalls simName implName plans))
  | _ => return stx

/-- Project a result leaf onto the impl field. With `field0? = none` (a non-split return such as
`UInt64`) there is no field to project, so the leaf is returned unchanged. -/
private meta def projectLeaf (field0? : Option Name) (stx : Term) : MacroM Term := do
  match field0? with
  | none        => pure stx
  | some field0 => `($stx.$(mkIdent field0):ident)

mutual
/-- Project the tail of a `doSeq` (the last `doSeqItem`): a terminal `doExpr` is projected as a term;
`doIf`/`doMatch` recurse into their branch sequences; binding items (`let`, `←`) are left alone. -/
private meta partial def projectDoSeqTail (implName : Name) (field0? : Option Name) (doSeq : Syntax) : MacroM Syntax := do
  let items := doSeq[0]
  if items.getNumArgs == 0 then return doSeq
  let lastIdx := items.getNumArgs - 1
  let lastItem := items[lastIdx]
  let stmt ← projectDoItem implName field0? lastItem[0]
  return doSeq.setArg 0 (items.setArg lastIdx (lastItem.setArg 0 stmt))

/-- Project a single tail `doSeqItem` statement. -/
private meta partial def projectDoItem (implName : Name) (field0? : Option Name) (stmt : Syntax) : MacroM Syntax := do
  if stmt.isOfKind ``Parser.Term.doExpr then
    return stmt.setArg 0 (← projectResultTail implName field0? ⟨stmt[0]⟩)
  else if stmt.isOfKind ``Parser.Term.doIf then
    -- `doIf` = `if <prop> then <thenSeq> [else <elseSeq>]`: project both branch sequences ([3], [5]).
    let stmt := stmt.setArg 3 (← projectDoSeqTail implName field0? stmt[3])
    if stmt[5].getNumArgs > 0 then
      return stmt.setArg 5 (stmt[5].setArg 1 (← projectDoSeqTail implName field0? stmt[5][1]))
    else return stmt
  else if stmt.isOfKind ``Parser.Term.doMatch then
    -- `doMatch … with <matchAlts>`: project each alt's rhs `doSeq` (the alt's last child).
    let altsIdx := stmt.getNumArgs - 1
    let altsNode := stmt[altsIdx]
    let alts' ← altsNode[0].getArgs.mapM fun alt => do
      let rhsIdx := alt.getNumArgs - 1
      pure (alt.setArg rhsIdx (← projectDoSeqTail implName field0? alt[rhsIdx]))
    return stmt.setArg altsIdx (altsNode.setArg 0 (altsNode[0].setArgs alts'))
  else
    return stmt

private meta partial def projectResultTail (implName : Name) (field0? : Option Name) (stx : Term) : MacroM Term := do
  match stx with
  | `(let $d:letDecl
      $body) =>
    let body' ← projectResultTail implName field0? body
    `(let $d:letDecl
      $body')
  | `(if $c then $t else $e) =>
    let t' ← projectResultTail implName field0? t
    let e' ← projectResultTail implName field0? e
    `(if $c then $t' else $e')
  | `(if $h : $c then $t else $e) =>
    let t' ← projectResultTail implName field0? t
    let e' ← projectResultTail implName field0? e
    `(if $h : $c then $t' else $e')
  | `(some $e) => if isCallOf implName e then pure stx else `(some $(← projectLeaf field0? e))
  | `(none)    => `(none)
  | _ =>
    -- `match`: project each alternative's right-hand side (the alternatives node is `match`'s last
    -- child; each `matchAlt`'s rhs is its last child).
    if stx.raw.isOfKind ``Parser.Term.match then
      let altsIdx := stx.raw.getNumArgs - 1
      let altsNode := stx.raw[altsIdx]
      let alts' ← altsNode[0].getArgs.mapM fun alt => do
        let rhsIdx := alt.getNumArgs - 1
        let rhs' ← projectResultTail implName field0? ⟨alt[rhsIdx]⟩
        pure (alt.setArg rhsIdx rhs')
      let altsNode' := altsNode.setArg 0 (altsNode[0].setArgs alts')
      return ⟨stx.raw.setArg altsIdx altsNode'⟩
    -- `do` block: descend into its `doSeq` tail. The block already returns `Option <buf>` via its
    -- (rewritten) tail, so a self-call tail is left untouched.
    else if stx.raw.isOfKind ``Parser.Term.do then
      return ⟨stx.raw.setArg 1 (← projectDoSeqTail implName field0? stx.raw[1])⟩
    -- `rlet pat ← expr rest` (a tail-continuation term macro): the tail is its `rest`, the last child.
    else if stx.raw.getNumArgs > 0 && stx.raw[0].isToken "rlet" then
      let lastIdx := stx.raw.getNumArgs - 1
      let rest' ← projectResultTail implName field0? ⟨stx.raw[lastIdx]⟩
      return ⟨stx.raw.setArg lastIdx rest'⟩
    else if isCallOf implName stx then
      return stx
    else
      projectLeaf field0? stx
end

/--
The field-0 accessor name (`buf`/`impl`) of `funcSim`'s return split type, for result projection.
Returns `none` for a *non-split* return (e.g. `UInt64`), where there is no field to project and the
result leaves are left as the bare impl value.
-/
private meta def buffedReturnField0 (declName : Name) : MetaM (Option Name) := do
  let info ← getConstInfo declName
  forallTelescopeReducing info.type fun _ retTy => do
    let retTy ← whnf retTy
    -- The return is either a bare split type or `Option (split type)`.
    let inner ← if let some #[i] := appOf? ``Option 1 retTy then whnf i else pure retTy
    let some rule := splitRuleOf? inner
      | -- Non-split return: no field projection (the `Sim` value *is* the impl).
        return none
    let some sInfo := getStructureInfo? (← getEnv) rule.typeName
      | throwError "@[buffed]: expected a structure type for {rule.typeName}"
    return some sInfo.fieldNames[0]!

namespace Veir.Buffed

/--
Prepend the structured-rebinding `let`s (edit 1) so the verbatim-copied body sees its original
parameters: `let ctx := ⟨ctx_buf, GHOST_ctx_spec, ctx_sim⟩` for each split parameter `ctx`.
-/
private meta def prependRebindLets (plans : Array ParamPlan) (body : Term) : MacroM Term := do
  let mut body := body
  for plan in plans.reverse do
    if let some structType := plan.structType? then
      -- `let ctx : Sim.IRContext OpInfo := ⟨ctx_buf, GHOST_ctx_spec, ctx_sim⟩`; the ascription lets
      -- the anonymous constructor pick the right structure. The ascribed type may mention another
      -- split parameter (`… [blockPtr.spec]`), so substitute those too.
      let structType' : Term := ⟨← substSplitIdents plans structType⟩
      let fields := plan.implFieldNames.map (mkIdent ·)
      let lhs := mkIdent plan.userName
      body ← `(let $lhs:ident : $structType' := ⟨$fields,*⟩
               $body)
  return body

end Veir.Buffed

open Lean Elab Command Veir.Buffed

/--
`<modifiers> buffed def fooSim … := …` elaborates the `Sim`-level definition, then generates
`fooImpl`, `fooSpec`, and the non-suffixed base wrapper from it. Replaces the old `@[buffed]`
attribute. Two optional flags may be placed right after `buffed`, in order:
- `(inline := false)` — keep the generated `<name>Impl` out of line (matches the attribute's flag);
  defaults to `true`.
- `(def_lemma := false)` — skip generating the `<name>_def` lemma relating the base wrapper to
  `<name>Sim`; defaults to `true`. Useful for definitions whose `_def` proof recipe does not apply
  (e.g. a `partial_fixpoint` recursion, where `fun_induction <name>Sim` has no induction principle).

Each flag's leading `(<kw>` is `atomic`, so the optional groups backtrack cleanly: writing only
`(def_lemma := …)` doesn't trip the `(inline := …)` group on the shared `(`.

`buffed` is a *declaration modifier* — it sits between the standard modifiers (docstring, `@[…]`) and
`def`, just like `noncomputable`/`partial`, so it composes with docComments, attributes, and
`set_option … in` without ordering surprises.
-/
syntax (name := buffedCmd)
  declModifiers "buffed"
    (atomic(ppSpace "(" &"inline") " := " (&"true" <|> &"false") ")")?
    (atomic(ppSpace "(" &"def_lemma") " := " (&"true" <|> &"false") ")")? ppSpace
    Parser.Command.definition : command

/--
Prepend `@[inline]` to a definition's `declModifiers`, the same way one would write `@[inline] def …`
in source. The attribute must be present on the `Sim` declaration *before* it is elaborated and
compiled: the compiler bakes the inline flag into the base-phase LCNF decl (and thus into the
reduce-arity wrapper `<name>Sim._redArg` it later derives), so tagging the `Sim` *after* `elabCommand`
is too late — the cached mono code, and any `_redArg` split off from it, would stay out-of-line and
leak into the generated `<name>Impl`. We use an unhygienic `inline` identifier so it reads as
`@[inline]`, matching the recursive `<name>Impl` path.
-/
private meta def prependInlineModifier (mods : TSyntax ``Parser.Command.declModifiers) :
    CommandElabM (TSyntax ``Parser.Command.declModifiers) := do
  let attrId := mkIdentFrom (← getRef) `inline (canonical := true)
  let attr ← `(Parser.Term.attrInstance| $attrId:ident)
  -- `declModifiers[1]` is the optional attributes node; empty when the source wrote no `@[…]`.
  let raw := mods.raw
  let attrsOpt := raw[1]
  if attrsOpt.getNumArgs == 0 then
    let attrs ← `(Parser.Term.attributes| @[$attr:attrInstance])
    return ⟨raw.setArg 1 (mkNullNode #[attrs.raw])⟩
  else
    -- Existing `@[a, b]`: splice `inline` (with a separating `,`) onto the front of the attr list.
    let attrsNode := attrsOpt[0]
    let lst := attrsNode[1]
    let lst' := lst.setArgs (#[attr.raw, mkNullNode #[]] ++ lst.getArgs)
    return ⟨raw.setArg 1 (mkNullNode #[attrsNode.setArg 1 lst'])⟩

/--
Build the recursive `<name>Impl` as a fresh `def`: reuse the impl signature from `buildBuffedImpl`,
and rewrite `funcSim`'s source body with the three edits (rebind split params, self-call →
`<name>Impl` with exploded args, project the result). The `declValSimple` is kept whole so any
`termination_by`/`decreasing_by` rides along; only its body subterm is rewritten.
-/
private meta def buildRecursiveImplCmd (declName implName : Name) (inline : Bool) (defn : Syntax)
    : CommandElabM (TSyntax `command) := do
  let plans ← liftCoreM <| MetaM.run' (Veir.Buffed.buffedParamPlan declName)
  let (binders, retTy) ← buffedImplSig declName plans defn
  let field0? ← liftCoreM <| MetaM.run' (buffedReturnField0 declName)
  -- `defn` = `def declId optDeclSig declVal …`; the body is `declVal[1]` of a `declValSimple`,
  -- whose trailing `where`/`termination_by`/`decreasing_by` we keep by rewriting only `[1]`.
  let declVal := defn[3]
  let srcBody : Term := ⟨declVal[1]⟩
  let newBody ← liftMacroM do
    let b ← rewriteSelfCalls declName implName plans srcBody
    let b ← projectResultTail implName field0? ⟨b⟩
    prependRebindLets plans b
  let newDeclVal := declVal.setArg 1 newBody.raw
  -- Use an unhygienic attribute identifier so it reads as `@[inline]`, not `@[inline✝]`.
  let attrId := mkIdentFrom (← getRef) (if inline then `inline else `noinline) (canonical := true)
  let inlineAttr ← `(Parser.Term.attrInstance| $attrId:ident)
  -- `implName` is fully qualified; prefix `_root_` so the surrounding namespace is not prepended again.
  -- Declare the same universe parameters as `funcSim` so the signature's universe-polymorphic
  -- constants are satisfied.
  let levelParams := (← liftCoreM <| getConstInfo declName).levelParams
  let implId := mkIdent (`_root_ ++ implName)
  let declId ←
    if levelParams.isEmpty then `(Parser.Command.declId| $implId)
    else
      let us := levelParams.toArray.map (mkIdent ·)
      `(Parser.Command.declId| $implId.{$us,*})
  let binderStx : TSyntaxArray ``Parser.Term.bracketedBinder := binders.map (⟨·⟩)
  let declValStx : TSyntax ``Parser.Command.declVal := ⟨newDeclVal⟩
  let cmd ← `(@[$inlineAttr] def $declId $binderStx* : $retTy $declValStx:declVal)
  trace[Buffed.ghosting.defs] "Generated recursive impl for {declName}:\n{cmd}"
  return cmd

elab_rules : command
  | `($mods:declModifiers buffed $[(inline := $inlineFlag?)]? $[(def_lemma := $defLemmaFlag?)]? $defn:definition) => do
    -- Both flags default to `true`. A flag's value token is `false` only when written `:= false`.
    let inline := match inlineFlag? with
      | none => true
      | some f => f.raw.getKind != `token.false
    let defLemma := match defLemmaFlag? with
      | none => true
      | some f => f.raw.getKind != `token.false
    -- `Sim` declarations are always inline. We inject `@[inline]` into the modifiers *before*
    -- elaborating, so the flag is present when the compiler lowers the `Sim` def to LCNF — otherwise
    -- its reduce-arity wrapper `<name>Sim._redArg` is split off without it and leaks an out-of-line
    -- call into the generated `<name>Impl`. (`inline := false` only ever controls the generated
    -- `<name>Impl`, never the always-inline `Sim`.)
    let mods ← prependInlineModifier mods
    -- Re-attach the modifiers to the bare `def` and elaborate the user's `Sim` definition as written.
    let cmd ← `($mods:declModifiers $defn:definition)
    elabCommand cmd
    -- Recover the declaration name from the `declId` and qualify it with the current namespace.
    let some declId := cmd.raw.find? (·.getKind == ``Parser.Command.declId)
      | throwError "buffed: could not find the definition's name"
    let declName := (← getCurrNamespace) ++ declId[0].getId
    -- Detect recursion from the *source* body (the elaborated value compiles self-calls into
    -- `brecOn`/`WellFounded.fix`, hiding the literal self-reference).
    let body := defn.raw[3][1]
    if mentionsCall declName body then
      -- Recursive: emit a genuinely recursive `<name>Impl`, then spec + base from the Sim term.
      let implName := Veir.Buffed.mkImplName declName
      unless (← getEnv).contains implName do
        elabCommand (← buildRecursiveImplCmd declName implName inline defn.raw)
      -- Emit the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)`, proved by
      -- induction along `<name>Sim` (see `mkRecursiveImplLemmaProof`). Skipped when
      -- `(def_lemma := false)`: its `fun_induction <;> grind` proof is what tends to fail (and even
      -- its `sorry` fallback can hard-error on unusual shapes), so opting out of `def_lemma` opts out
      -- of this lemma too. Downstream base/spec generation that relies on `<name>_impl` (via
      -- `rebuildIRContextWithProvenSim`) then degrades gracefully to a `sorry` `sim` proof.
      if defLemma then
        liftCoreM <| generateBuffedImplLemma declName (recursive := true)
      liftCoreM <| generateBuffedSpecAndBase declName (recursive := true)
      -- Emit the `<name>_def` lemma `<base> args = <name>Sim args` by induction along `<name>Sim`,
      -- e.g. the hand-written `Rewriter.detachOperands.loop_def`. Skipped when `(def_lemma := false)`,
      -- e.g. a `partial_fixpoint` def where `fun_induction <name>Sim` has no induction principle.
      if defLemma then
        liftCoreM <| generateBuffedDefLemma declName (recursive := true)
    else
      liftCoreM <| generateBuffed declName inline (defLemma := defLemma)

initialize registerTraceClass `Buffed.ghosting (inherited := false)
initialize registerTraceClass `Buffed.ghosting.defs (inherited := false)
