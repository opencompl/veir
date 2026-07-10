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
  cases x <;> grind

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

/-- Replace a trailing `Sim` suffix on `n`'s final component with `suffix` (appending `suffix` if there is no `Sim` to drop). -/
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

/-- Turn `fooSim` into `foo_impl` (the name of the generated lemma relating `(fooSim …).impl` to `fooImpl` applied to the projected arguments). -/
private meta def mkImplLemmaName : Name → Name := renameSim "_impl"

/-- Table entry describing how to split/rebuild a structured argument. -/
private structure BuffedSplitRule where
  typeName : Name
  ctorName : Name
  fieldSuffixes : Array String

/-- Build a plain two-field `impl`/`spec` split rule for the structure `typeName`/`ctorName`. -/
private meta def implSpecRule (typeName ctorName : Name) : BuffedSplitRule :=
  { typeName, ctorName, fieldSuffixes := #["impl", "spec"] }

/-- Known structures that `@[buffed]` should split into field arguments. -/
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

/-- Whether `e`'s head constant is `Sim.IRContext` or a structure in the split table — i.e. a type that `@[buffed]` splits into `impl`/`spec` fields. -/
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

/-- Expand Sim-structured arguments into the flattened argument list expected by `<name>Impl`. -/
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

/-- Project field `fieldIdx` (0 = `impl`, 1 = `spec`) out of `e`, descending through `Option` and `Prod` to reach the underlying split type. -/
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
    -- Dependent pair: project each component, then re-pack with an explicit type family.
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
      -- `named` selects the displayed form: `mkProjection` builds the named projection `e.<field>` (for the `_impl` lemma *statement*), while `mkProj` is the raw indexed projection used when *defining* `<name>Impl`/`<name>Spec`/base.
      if named then
        let some sInfo := getStructureInfo? (← getEnv) typeName
          | throwError "@[buffed]: expected a structure type for {typeName}"
        mkProjection e sInfo.fieldNames[fieldIdx]!
      else
        pure (mkProj typeName fieldIdx e)
    else
      throwError "@[buffed]: field index {fieldIdx} out of bounds for {typeName}"

/-- Re-project then reassemble `e` (definitionally equal to it), descending through `Option`, `Prod`, and dependent `Sigma`. -/
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
    -- Dependent pair: the second component's type mentions the first, so we keep `Sigma`'s type family `β` explicit instead of letting `mkAppM` infer it.
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
              -- Spec fields are ghost (erased) data; prefix them with `GHOST_` so the generated `<name>Impl` parameter names (e.g. `GHOST_ctx_spec`) flag them as such.
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

/-- Classification of the return type of a Sim-level definition, telling `buildBuffedBase` how to reassemble the result from the generated `<name>Impl`/`<name>Spec` calls. -/
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
    -- `IRContext` (three fields, a `sim` proof) is handled above; only plain `impl`/`spec` pairs have the two-argument constructor `optionSplit` relies on.
    if let some rule := splitRuleOf? innerWhnf then
      if rule.fieldSuffixes == #["impl", "spec"] then
        return .optionSplit rule
  return .other

/-- Unwrap `o : Option α` as `o.specGet!` (i.e. `o.get!`, spelled with `Option.get` so the impl projection drops the spec cleanly). -/
private meta def mkOptionGetSorry (o : Expr) : MetaM Expr := do
  mkAppM ``Option.specGet! #[o]

/-- Build `IRContext.mk buf spec sim : targetTy`, leaving the erased `sim` proof as `sorry`; the type arguments come from `targetTy`. -/
private meta def rebuildIRContextWithSorrySim (targetTy buf spec : Expr) : MetaM Expr := do
  -- `IRContext.mk`'s leading implicit args mirror `Sim.IRContext`'s own parameters (`OpInfo`, `inst`), so we copy exactly those from `targetTy` rather than hard-coding their count.
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

/-- Build `IRContext.mk buf spec <proof> : targetTy` where the `sim` proof is *proven* (not `sorry`) from the `<name>_impl` lemma, for a recursive bare-`IRContext`-returning def. -/
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
  -- Feed the lemma application / spec constant to `simp only` as terms, and close with the `sim` projection of the `Sim`-level call.
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

/-- Build the *whole* base body for an `Option (IRContext …)`-returning non-recursive def as a `match` on `<name>Impl …`, with the `sim` proof *proven* (not `sorry`), avoiding the `Subtype`-projection-over- erased-`attach`-wrapper shape entirely: match h : <name>Impl (projected xs) with -/
private meta def mkOptionIRContextMatchBody (declName : Name) (us : List Level) (xs : Array Expr)
    (innerTy implBody specBody : Expr) : Lean.Elab.TermElabM Expr := do
  -- Splice the impl-call discriminant and the spec call in as *pre-built `Expr`s* via `exprToSyntax` (a syntax leaf that re-elaborates to exactly that expr), NOT via delaboration: `implBody`/`specBody` mention erased proof projections (e.g. `ctx.sim`) that a delaborate→re-elaborate roundtrip would turn into leaked metavariables.
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
  let expectedTy ← mkAppM ``Option #[innerTy]
  let body ← Lean.Elab.Term.elabTermEnsuringType bodyStx (some expectedTy)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars body

/-- Combine an impl-projection value `impl` and a spec-projection value `spec` back into the original split shape described by `simInnerTy` (a `<name>Sim` result without its outer `Option`). -/
private meta partial def mkBuffedCombine (simInnerTy impl spec : Expr) : MetaM Expr := do
  let ty ← whnf simInnerTy
  if let some #[a, b] := appOf? ``Prod 2 ty then
    let fst ← mkBuffedCombine a (← mkAppM ``Prod.fst #[impl]) (← mkAppM ``Prod.fst #[spec])
    let snd ← mkBuffedCombine b (← mkAppM ``Prod.snd #[impl]) (← mkAppM ``Prod.snd #[spec])
    mkAppM ``Prod.mk #[fst, snd]
  else if let some #[a, β] := appOf? ``Sigma 2 ty then
    -- Dependent pair: keep `Sigma`'s type family `β` explicit (`mkAppM` cannot infer the dependent motive).
    let fst ← mkBuffedCombine a (← mkAppM ``Sigma.fst #[impl]) (← mkAppM ``Sigma.fst #[spec])
    let snd ← mkBuffedCombine (β.beta #[fst]) (← mkAppM ``Sigma.snd #[impl]) (← mkAppM ``Sigma.snd #[spec])
    pure (mkAppN (mkConst ``Sigma.mk ty.getAppFn.constLevels!) #[a, β, fst, snd])
  else if ty.getAppFn.constName? == some ``Veir.Sim.IRContext then
    rebuildIRContextWithSorrySim ty impl spec
  else if !isSplitType ty then
    -- Non-split leaf (e.g. `UInt64`): `impl` and `spec` are the same value, so just return the impl.
    pure impl
  else
    let some typeName := ty.getAppFn.constName?
      | throwError "@[buffed]: cannot combine impl/spec at type {ty}"
    let some rule := findBuffedSplitRule? typeName
      | throwError "@[buffed]: no split rule registered for {typeName}"
    mkAppM rule.ctorName #[impl, spec]

/-- Whether the split shape `ty` (descending `Prod`/`Sigma`) contains a `Sim.IRContext` leaf — i.e. a leaf whose `sim` field `mkBuffedCombine` would fill with `sorry`. -/
private meta partial def splitShapeHasIRContext (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  if let some #[a, b] := appOf? ``Prod 2 ty then
    return (← splitShapeHasIRContext a) || (← splitShapeHasIRContext b)
  else if let some #[a, β] := appOf? ``Sigma 2 ty then
    -- Instantiate the `Sigma` family at a fresh fvar to inspect the second component's shape.
    let hasB ← forallTelescopeReducing (← inferType β) fun ys _ =>
      if let some y := ys[0]? then splitShapeHasIRContext (β.beta #[y]) else pure false
    return (← splitShapeHasIRContext a) || hasB
  else
    return ty.getAppFn.constName? == some ``Veir.Sim.IRContext

/-- Syntactically recombine the impl value `xTerm` and spec value `specTerm` back into the split shape `simInnerTy` (a `<name>Sim` result without its outer `Option`), producing a `Term` in which every `Sim.IRContext` leaf carries a *proven* `sim` field (not `sorry`). -/
private meta partial def mkProvenCombineSyntax (simInnerTy : Expr)
    (xTerm specTerm simGetTerm implLemmaTerm simTerm : Lean.Term) (specId : Lean.Ident) :
    Lean.Elab.TermElabM Lean.Term := do
  let ty ← whnf simInnerTy
  let getId := mkIdent ``Option.specGet!
  if let some #[a, b] := appOf? ``Prod 2 ty then
    let fst ← mkProvenCombineSyntax a (← `($xTerm.1)) (← `($specTerm.1)) (← `($simGetTerm.1))
      implLemmaTerm simTerm specId
    let snd ← mkProvenCombineSyntax b (← `($xTerm.2)) (← `($specTerm.2)) (← `($simGetTerm.2))
      implLemmaTerm simTerm specId
    `(($fst, $snd))
  else if let some #[a, β] := appOf? ``Sigma 2 ty then
    let fst ← mkProvenCombineSyntax a (← `($xTerm.1)) (← `($specTerm.1)) (← `($simGetTerm.1))
      implLemmaTerm simTerm specId
    let snd ← mkProvenCombineSyntax (β.beta #[← Lean.Elab.Term.elabTerm fst none]) (← `($xTerm.2))
      (← `($specTerm.2)) (← `($simGetTerm.2)) implLemmaTerm simTerm specId
    `(⟨$fst, $snd⟩)
  else if ty.getAppFn.constName? == some ``Veir.Sim.IRContext then
    let ctorId := mkIdent ``Veir.Sim.IRContext.mk
    -- The leaf `sim` proof: bind this leaf's already-proven `sim` (`simGetTerm.sim`, where `simGetTerm` is the projection of `(<name>Sim xs).specGet!` at this leaf's path) as a hypothesis `hs` *before* casing, so `simp_all` rewrites it in lockstep.
    let simProof ← `(term| (by
      have := $implLemmaTerm:term
      have hs := ($simGetTerm).sim
      simp only [$specId:ident, $getId:ident, Option.map, Option.get!] at *
      cases hc : $simTerm:term <;> simp_all <;> subst_vars <;> exact hs))
    `($ctorId:ident $xTerm $specTerm $simProof)
  else if !isSplitType ty then
    -- Non-split leaf (e.g. `UInt64`): impl and spec coincide, so just return the impl value.
    pure xTerm
  else
    let some typeName := ty.getAppFn.constName?
      | throwError "@[buffed]: cannot combine impl/spec at type {ty}"
    let some rule := findBuffedSplitRule? typeName
      | throwError "@[buffed]: no split rule registered for {typeName}"
    `($(mkIdent rule.ctorName) $xTerm $specTerm)

/-- Build the *whole* base body for an `Option (split shape containing `IRContext`)`-returning non-recursive def as a `match h : <name>Impl … with | none => none | some x => some <combined>`, where `<combined>` reassembles the split shape from the matched impl value `x` and `(<name>Spec xs).specGet!` with every `IRContext` leaf's `sim` field *proven* (not `sorry`) — see `mkProvenCombineSyntax`. -/
private meta def mkOptionOtherMatchBody (declName : Name) (us : List Level) (xs : Array Expr)
    (innerSimTy implBody specBody : Expr) : Lean.Elab.TermElabM Expr := do
  -- Splice the impl discriminant as a pre-built `Expr` (no delaborate→re-elaborate roundtrip that would turn erased proof projections into leaked mvars); delaborate only the `<name>_impl` lemma app (so its autoParam args stay pinned) and the `<name>Sim`/`<name>Spec` calls (used only inside the `by` proofs).
  let implStx ← Lean.Elab.Term.exprToSyntax implBody
  let specStx ← Lean.Elab.Term.exprToSyntax specBody
  let implLemmaApp := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let implLemmaTerm ← Lean.PrettyPrinter.delab implLemmaApp
  let simTerm ← Lean.PrettyPrinter.delab (mkAppN (mkConst declName us) xs)
  let specId := mkIdent (mkSpecName declName)
  let specGetTerm ← `(($specStx).specGet!)
  let simGetTerm ← `(($simTerm).specGet!)
  let combined ← mkProvenCombineSyntax innerSimTy (← `(x)) specGetTerm simGetTerm implLemmaTerm simTerm specId
  let bodyStx ← `(term|
    match h : $implStx:term with
    | none => none
    | some x => some $combined)
  let expectedTy ← mkAppM ``Option #[innerSimTy]
  let body ← Lean.Elab.Term.elabTermEnsuringType bodyStx (some expectedTy)
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  instantiateMVars body

/-- Build the generated non-suffixed wrapper, combining generated `<name>Impl` and `<name>Spec`. -/
meta def buildBuffedBase (declName : Name) (recursive : Bool) (defLemma : Bool := true) :
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
    -- `Option (split type)` and `Option (IRContext …)` share one shape: drive the `some`/`none` off `<name>Impl` and recover the spec component from `<name>Spec` only in the `some` branch, i.e.
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
          -- For a recursive def `<name>Impl`/`<name>Spec` are independent functions, no longer defeq to projections of `<name>Sim`.
          if defLemma then
            rebuildIRContextWithProvenSim declName us xs callTy implBody specBody
          else
            rebuildIRContextWithSorrySim callTy implBody specBody
        else
          let simProof := mkProj ``Veir.Sim.IRContext 2 call
          mkAppM ``Veir.Sim.IRContext.mk #[implBody, specBody, simProof]
      | .bareSplit rule =>
        -- Assemble from calls to the generated `<name>Impl`/`<name>Spec` so the base actually *invokes* `<name>Spec` (preserving its `@[noinline]`/`@[nospecialize]`) instead of re-projecting `call`, which would unfold the spec body inline.
        mkAppM rule.ctorName #[implBody, specBody]
      | .optionSplit rule =>
        mapSomeOverImpl fun x specGet => mkAppM rule.ctorName #[x, specGet]
      | .optionIRContext innerTy =>
        -- Both the recursive and non-recursive Option-`IRContext` bases use the same `match h : <name>Impl … with | none => none | some buf => some ⟨buf, (<name>Spec …).specGet!, <proof-using-h>⟩` shape, *proving* the `sim` field from the `<name>_impl` lemma (cf. the hand-written `Sim.OperationPtr.setParentWithCheck!`).
        if !defLemma || (recursive && !(← getEnv).contains (mkImplLemmaName declName)) then
          mapSomeOverImpl fun x specGet => rebuildIRContextWithSorrySim innerTy x specGet
        else
          mkOptionIRContextMatchBody declName us xs innerTy implBody specBody
      | .other =>
        -- Remaining product / dependent-`Sigma` returns (possibly under `Option`).
        if let some #[innerSimTy] := appOf? ``Option 1 callTy then
          -- When the shape has an `IRContext` leaf (whose `sim` field the plain `Option.map` combine would fill with `sorry`), build a `match h : <name>Impl … with | some x => some <combined>` instead and *prove* every leaf `sim` from the `<name>_impl` lemma (see `mkOptionOtherMatchBody`) — the same technique as `mkOptionIRContextMatchBody`, which the plain `Option.map` lambda cannot use (it severs the connection to `<name>Sim`).
          if defLemma && (← splitShapeHasIRContext innerSimTy) && (← getEnv).contains (mkImplLemmaName declName) then
            mkOptionOtherMatchBody declName us xs innerSimTy implBody specBody
          else
            mapSomeOverImpl fun x specGet => mkBuffedCombine innerSimTy x specGet
        else
          mkBuffedCombine callTy implBody specBody
    let baseTy ← inferType baseBody
    let baseForall ← mkForallFVars xs baseTy
    let baseLambda ← mkLambdaFVars xs baseBody
    pure (baseName, baseForall, baseLambda, info.levelParams)

/-- How `<name>_def` (`<base> args = <name>Sim args`) is proved for return shape `shape`. -/
private inductive DefLemmaProof where
  /-- The base wrapper is *definitionally equal* to `funcSim`, so `Eq.refl` discharges it. -/
  | rfl
  /-- An `Option`-returning base wrapper. -/
  | optionTactic
  /-- An `Option (IRContext …)`-returning base wrapper, reassembled via `match h : <name>Impl … with …` with a *proven* `sim` field (`mkOptionIRContextMatchBody`). -/
  | optionIRContextTactic
  /-- The `Prod`/`Sigma` (`.other`) base wrapper is reassembled component-wise (`mkBuffedCombine`), so it is *not* defeq to `funcSim`. -/
  | otherTactic

/-- How to prove the `<name>_def` lemma for return shape `shape` (see `DefLemmaProof`). -/
private meta def defLemmaProofFor : BaseReturnShape → DefLemmaProof
  | .irContext | .bareSplit _ => .rfl
  | .optionSplit _ => .optionTactic
  | .optionIRContext _ => .optionIRContextTactic
  | .other => .otherTactic

/-- Build the proof term for an `Option`-returning `<name>_def` lemma. -/
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

/-- Build the proof term for an `Option (IRContext …)`-returning `<name>_def` lemma. -/
private meta def mkOptionIRContextDefLemmaProof (declName baseName : Name) (us : List Level)
    (xs : Array Expr) (instGoalTy : Expr) : Lean.Elab.TermElabM Expr := do
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let specId := mkIdent (mkSpecName declName)
  let getId := mkIdent ``Option.specGet!
  -- `<name>_impl` applied to the explicit telescope args, delaborated to a term so the autoParam args are pinned (a bare `<name>_impl` would re-synthesize its `:= by grind` autoParams).
  let implLemmaApp := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let implTerm ← Lean.PrettyPrinter.delab implLemmaApp
  -- Template: strip the `sim` field via `option_ext`, unfold the base, add `<name>_impl xs` as a fact, then `split` the match and close each branch with `simp_all [<name>Spec, Option.specGet!]` (which chains `<name>_impl` with the branch equation `<name>Impl … = none`/`= some buf` and case-splits `<name>Sim xs` via `Option.map_eq_none`/`_some`) finishing with `grind` (cf. the hand-written `Sim.OperationPtr.setAttributes_def_EXAMPLE`).
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

/-- Build the proof term for a `Prod`/`Sigma`-under-`Option` (`.other`) `<name>_def` lemma whose base is the proven-`sim` `match h : <name>Impl … with | some x => some <combined>` shape (`mkOptionOtherMatchBody`), i.e. a shape with an `IRContext` leaf. -/
private meta def mkOptionOtherDefLemmaProof (declName baseName : Name) (us : List Level)
    (xs : Array Expr) (instGoalTy : Expr) : Lean.Elab.TermElabM Expr := do
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let specId := mkIdent (mkSpecName declName)
  let getId := mkIdent ``Option.specGet!
  let implLemmaApp := mkAppN (mkConst (mkImplLemmaName declName) us) xs
  let implTerm ← Lean.PrettyPrinter.delab implLemmaApp
  -- Reduce the `Option (…)` equality pointwise (`Option.ext`), add `<name>_impl xs` as a fact, unfold the base, then `split` the base's `match` and close each branch with `simp_all [<name>Spec, Option.specGet!] <;> grind`.
  let grindHints ← (#[``Veir.Sim.IRContext] ++ buffedSplitTable.map (·.typeName)).mapM
    fun n => `(Lean.Parser.Tactic.grindParam| $(mkIdent n):ident)
  let templateTac ← `(tactic|
    (apply Option.ext
     intro a
     have := $implTerm:term
     unfold $baseId:ident
     split <;>
       simp_all [$specId:ident, $getId:ident, Option.map_eq_some_iff] <;>
       grind [$grindHints,*]))
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

/-- Build the proof term for a `Prod`/`Sigma` (`.other`) `<name>_def` lemma of type `goalTy` (the full `∀ xs, <base> xs = <name>Sim xs`). -/
private meta def mkOtherDefLemmaProof (baseName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let tac ← `(tactic| (intros; simp only [$baseId:ident, $declId:ident]; grind))
  Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
  instantiateMVars goalMVar

/-- Build the proof term for a *recursive* `<name>_def` lemma of type `goalTy` (the full `∀ xs, <base> xs = <name>Sim xs`). -/
private meta def mkRecursiveDefLemmaProof (baseName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let baseId := mkIdent baseName
  let declId := mkIdent declName
  let tac ← `(tactic| (intros; fun_induction $declId:ident <;> grind (gen := 20) [$baseId:ident]))
  Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
  instantiateMVars goalMVar

/-- Build the proof term for a recursive *bare-`IRContext`* `<name>_def` lemma of type `goalTy` (`∀ xs, <base> xs = <name>Sim xs`). -/
private meta def mkRecursiveIRContextDefLemmaProof (baseName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let goalMVar ← mkFreshExprSyntheticOpaqueMVar goalTy
  let baseId := mkIdent baseName
  let specId := mkIdent (mkSpecName declName)
  let implId := mkIdent (mkImplLemmaName declName)
  -- `simp only` (rather than `rw`) handles the dependent rewrite under the `sim` proof field; after unfolding the base and `<name>Spec` and rewriting `buf` back via `← <name>_impl`, the goal closes.
  let tac ← `(tactic|
    (intros; simp only [$baseId:ident, $specId:ident, ← $implId:ident]))
  Lean.Elab.Term.runTactic goalMVar.mvarId! tac .term
  instantiateMVars goalMVar

/-- Build the proof term for a *recursive* `<name>_impl` lemma of type `goalTy` (the full `∀ xs, (funcSim args).impl = funcImpl (projected args)`). -/
private meta def mkRecursiveImplLemmaProof (implName declName : Name) (goalTy : Expr) :
    Lean.Elab.TermElabM Expr := do
  let implId := mkIdent implName
  let declId := mkIdent declName
  -- `grind` hints: the split structures from `buffedSplitTable` (`Sim.IRContext` + every `Sim.*Ptr`), so `grind` reasons about their projections/eta when relating `<name>Sim` to `<name>Impl`.
  let grindHints ← (#[``Veir.Sim.IRContext] ++ buffedSplitTable.map (·.typeName)).mapM
    fun n => `(Lean.Parser.Tactic.grindParam| $(mkIdent n):ident)
  let tac ← `(tactic| (intros; fun_induction $declId:ident <;>
    (unfold $implId:ident
     grind (instances := 2000) [$grindHints,*])))
  -- Run the tactic with `Tactic.run`, which returns the *remaining* goals rather than logging an `unsolved goals` error.
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

/-- Build the `<name>_def` lemma `<base> args = <name>Sim args`, relating the generated base wrapper back to the original Sim-level definition (e.g. `getFirstUse ctx ptr ib = getFirstUseSim ctx ptr ib`). -/
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
      -- Recursive: base is an independent recursive function, so prove the equation by `fun_induction` (the defeq `rfl` proof no longer applies).
      if let .other := shape then return none
      -- A bare-`IRContext` base now carries a *proven* `sim` field referencing `<name>Sim`, which defeats `fun_induction <;> grind [<base>]`; use the unfold-and-rewrite recipe instead.
      let defProof ←
        if let .irContext := shape then
          mkRecursiveIRContextDefLemmaProof baseName declName defForall
        else if let .optionIRContext _ := shape then
          -- The recursive `Option (IRContext …)` base is a single non-recursive `match h : <name>Impl …` with a *proven* `sim` field (same shape as the non-recursive case; see `buildBuffedBase`).
          mkOptionIRContextDefLemmaProof declName baseName us xs eqTy >>= (mkLambdaFVars xs ·)
        else
          mkRecursiveDefLemmaProof baseName declName defForall
      return some (defName, defForall, defProof, info.levelParams)
    match defLemmaProofFor shape with
    | .rfl =>
      -- The two sides are defeq (structure eta), so `Eq.refl` discharges it.
      let defProof ← mkLambdaFVars xs (← mkEqRefl baseCall)
      return some (defName, defForall, defProof, info.levelParams)
    | .optionTactic =>
      -- Prove the *instantiated* goal `eqTy` with `xs` in scope (so the `_impl` lemma can be applied to the explicit args), then abstract the parameters back out.
      let instProof ← mkOptionDefLemmaProof declName baseName us xs eqTy
      let defProof ← mkLambdaFVars xs instProof
      return some (defName, defForall, defProof, info.levelParams)
    | .optionIRContextTactic =>
      -- The `Option (IRContext …)` base uses `match h : <name>Impl … with …` with a proven `sim`; the dependent match blocks the plain `optionTactic` `rfl`, so use the `split <;> cases … <;> simp_all` recipe.
      let instProof ← mkOptionIRContextDefLemmaProof declName baseName us xs eqTy
      let defProof ← mkLambdaFVars xs instProof
      return some (defName, defForall, defProof, info.levelParams)
    | .otherTactic =>
      -- When the base is the proven-`sim` `match h : <name>Impl …` shape (an `IRContext` leaf under `Option`; see `buildBuffedBase`/`mkOptionOtherMatchBody`), its dependent `sim` field blocks the plain `simp only [<base>, <name>Sim]; grind` recipe — use the `Option.ext`+`cases` recipe instead (`mkOptionOtherDefLemmaProof`), mirroring the `.optionIRContext` case.
      let usesMatchBase ← do
        if let some #[innerSimTy] := appOf? ``Option 1 callTy then
          pure ((← splitShapeHasIRContext innerSimTy) && (← getEnv).contains (mkImplLemmaName declName))
        else pure false
      if usesMatchBase then
        let instProof ← mkOptionOtherDefLemmaProof declName baseName us xs eqTy
        let defProof ← mkLambdaFVars xs instProof
        return some (defName, defForall, defProof, info.levelParams)
      else
        let defProof ← mkOtherDefLemmaProof baseName declName defForall
        return some (defName, defForall, defProof, info.levelParams)

/-- Build the proof term for a *non-recursive* `Option`-returning `<name>_impl` lemma of type `goalTy` (the full `∀ xs, Option.map (·.buf) (<name>Sim xs) = <name>Impl (projected xs)`). -/
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

/-- Build the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)`, relating the impl projection of the original `Sim`-level result to a call of the generated `<name>Impl` on the flattened (impl/spec-split) arguments — the same projection `buildBuffedImpl` performs to *define* `<name>Impl`. -/
meta def buildBuffedImplLemma (declName : Name) (recursive : Bool) (defLemma : Bool := true) :
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
    let lhs ← mkBuffedProj 0 simCall (named := true)
    -- RHS: `<name>Impl` applied to the flattened impl/spec-split arguments, projected by name (`ctx.buf`, `ptr.impl`, …) rather than by index.
    let implArgs ← mkImplArgsFrom xs (named := true)
    let rhs := mkAppN (mkConst implName us) implArgs
    let eqTy ← mkEq lhs rhs
    let implForall ← mkForallFVars xs eqTy
    let proof ←
      if recursive then
        mkRecursiveImplLemmaProof implName declName implForall
      else
        -- `Option`-returning shapes get the `unfold <name>Impl; grind` template proof — unless `def_lemma := false`, which opts out of all generated `grind` proofs; the lemma is then emitted with a `sorry` proof.
        match shape with
        | .optionSplit _ | .optionIRContext _ =>
          if defLemma then
            mkOptionImplLemmaProof implName implForall
          else
            mkSorry implForall (synthetic := false)
        | _ => mkLambdaFVars xs (← mkEqRefl lhs)
    pure (implLemmaName, implForall, proof, info.levelParams)

end Veir.Buffed

/-- Apply a bare attribute `@[<attrName>]` to an already-added declaration through the standard attribute machinery, exactly as if it were written `@[<attrName>]` in source. -/
private meta def applyBareAttr (name attrName : Name) : AttrM Unit := do
  let stx := Syntax.node .none ``Lean.Parser.Attr.simple #[mkIdent attrName, Syntax.node .none nullKind #[]]
  Attribute.add name attrName stx (kind := .global)

/-- Set the inline attribute for an already-added declaration through the `@[inline]`/`@[noinline]` attribute syntax (the same path the recursive `<name>Impl` uses). -/
private meta def setInlineAttr (name : Name) (inline? : Bool := true) : AttrM Unit := do
  trace[Buffed.ghosting] "Setting inline attribute for {name} to {inline?}"
  if inline? then
    applyBareAttr name `inline
  else
    applyBareAttr name `noinline

/-- Add a generated declaration `(name, type, value, levelParams)`, tag its inline attribute, then compile it. -/
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

/-- Add a generated theorem `(name, type, value, levelParams)`. -/
private meta def addBuffedThm (name : Name) (type value : Expr) (levelParams : List Name) : AttrM Unit := do
  addDecl <| .thmDecl { name, levelParams, type, value }

/-- Emit the `<name>_def` lemma relating the base wrapper to `funcSim`, unless it already exists or the return shape has no `_def`. -/
private meta def generateBuffedDefLemma (decl : Name) (recursive : Bool) : AttrM Unit := do
  let defName := Veir.Buffed.mkDefName decl
  unless (← getEnv).contains defName do
    if let some (defName, defType, defValue, defLevelParams) ←
        MetaM.run' (Veir.Buffed.buildBuffedDefLemma decl recursive).run' then
      trace[Buffed.ghosting] "Generating {defName} for {decl}"
      addBuffedThm defName defType defValue defLevelParams

/-- Emit the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)` (see `buildBuffedImplLemma`), unless it already exists. -/
private meta def generateBuffedImplLemma (decl : Name) (recursive : Bool) (defLemma : Bool := true) : AttrM Unit := do
  let implLemmaName := Veir.Buffed.mkImplLemmaName decl
  unless (← getEnv).contains implLemmaName do
    let (implLemmaName, implType, implValue, implLevelParams) ←
      MetaM.run' (Veir.Buffed.buildBuffedImplLemma decl recursive defLemma).run'
    trace[Buffed.ghosting] "Generating {implLemmaName} for {decl}"
    addBuffedThm implLemmaName implType implValue implLevelParams

/-- Generate the `<name>Spec` ghost projection and the non-suffixed base wrapper from `funcSim`. -/
private meta def generateBuffedSpecAndBase (decl : Name) (recursive : Bool) (defLemma : Bool := true) : AttrM Unit := do
  let specName := Veir.Buffed.mkSpecName decl
  unless (← getEnv).contains specName do
    trace[Buffed.ghosting] "Generating {specName} for {decl}"
    let (specName, specType, specValue, specLevelParams) ← MetaM.run' (Veir.Buffed.buildBuffedSpec decl)
    -- The spec is kept out of line (`@[noinline]`) and unspecialized (`@[nospecialize]`) so the impl never inlines it and no specialized copies of the ghost spec are generated.
    addBuffedDecl specName specType specValue specLevelParams (inline? := false) (nospecialize? := true)
  Lean.enableRealizationsForConst specName
  let baseName := Veir.Buffed.mkBaseName decl
  unless (← getEnv).contains baseName do
    trace[Buffed.ghosting] "Generating {baseName} for {decl}"
    let (baseName, baseType, baseValue, baseLevelParams) ← MetaM.run' (Veir.Buffed.buildBuffedBase decl recursive defLemma).run'
    addBuffedDecl baseName baseType baseValue baseLevelParams (inline? := true)
  Lean.enableRealizationsForConst baseName

/-- Generate `<name>Impl`, `<name>Spec`, and the non-suffixed base wrapper from an already-elaborated Sim-level definition `decl`. -/
meta def generateBuffed (decl : Name) (inline : Bool) (defLemma : Bool := true) : AttrM Unit := do
  Veir.Buffed.checkSim decl
  let implName := Veir.Buffed.mkImplName decl
  unless (← getEnv).contains implName do
    trace[Buffed.ghosting] "Generating {implName} for {decl}"
    let (implName, implType, implValue, levelParams) ← MetaM.run' (Veir.Buffed.buildBuffedImpl decl)
    addBuffedDecl implName implType implValue levelParams (inline? := inline)
  Lean.enableRealizationsForConst implName
  -- Emit the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)`.
  generateBuffedImplLemma decl (recursive := false) (defLemma := defLemma)
  generateBuffedSpecAndBase decl (recursive := false) (defLemma := defLemma)
  -- Emit the `<name>_def` lemma relating the base wrapper to `funcSim`.
  if defLemma then
    generateBuffedDefLemma decl (recursive := false)

/-! Recursive `<name>Impl` generation -/

namespace Veir.Buffed

open Lean Elab Command Term PrettyPrinter

/-- Per source parameter: how it maps to impl parameters and how to project it in the body. -/
private structure ParamPlan where
  /-- The user-facing name of the original `funcSim` parameter (e.g. `ctx`). -/
  userName : Name
  /-- For a split parameter, the structure's field accessor names (`#[buf, spec, sim]`); empty when the parameter passes through unchanged. -/
  fieldAccessors : Array Name := #[]
  /-- For a split parameter, the generated impl field-parameter names (`#[ctx_buf, GHOST_ctx_spec, ctx_sim]`), in field order. -/
  implFieldNames : Array Name := #[]
  /-- For a split parameter, its structure type as syntax (e.g. `Sim.IRContext OpInfo`), used to ascribe the rebinding `let`. -/
  structType? : Option Term := none
  /-- For a split parameter, the structure's constructor (e.g. `Sim.IRContext.mk`), used to spell the reconstructed value. -/
  ctorName? : Option Name := none
  /-- For a split parameter, each field's type as syntax (`#[IRBufContext OpInfo, IRContext OpInfo, Sim ctx_buf GHOST_ctx_spec]`), used as the generated impl field-parameter types. -/
  fieldTypes : Array Term := #[]

/-- Classify each explicit parameter of `funcSim` for the recursive body rewrite. -/
private meta def buffedParamPlan (declName : Name) : MetaM (Array ParamPlan) := do
  let info ← getConstInfo declName
  -- Delaborate field types with field notation off so dot-receivers like `ctx_sim`'s `Sim ctx_buf GHOST_ctx_spec` stay applicative and re-parse cleanly.
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
        -- Reconstruct each field's type with the impl field names bound as locals, so dependent fields (e.g. `sim : Sim ctx_buf GHOST_ctx_spec`) delaborate with the generated names.
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

/-- Substitute every split parameter identifier in `stx` with its reconstructed `Ctor.mk …` term, so a proof type like `ptr.InBounds ctx` becomes `(Sim.OperationPtr.mk ptr_impl …).InBounds (Sim.IRContext.mk …)`. -/
private meta partial def substSplitIdents (plans : Array ParamPlan) (stx : Syntax) : MacroM Syntax := do
  if stx.isIdent then
    let id := stx.getId.eraseMacroScopes
    -- Match either the whole ident (`ctx`) or its head component (`ctx` in `ctx.spec`).
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

/-- Build the recursive impl's `def` binders + return type. -/
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
        -- No split names: keep the binder verbatim — including any `:= by …` autoParam default, which self-calls may rely on — only substituting split identifiers in its type.
        let tyStx' : Term := ⟨← liftMacroM <| substSplitIdents plans tyStx⟩
        binders := binders.push (b.setArg 2 ((b[2]).setArg 1 tyStx'))
      else
        -- A binder may bind several names sharing one type (`(fromOp toOp : T)`); expand split names to their field binders and group consecutive non-split names.
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
              -- A field type may mention *another* split parameter (`Sim … [blockPtr.spec]`); rewrite those references to their reconstructed `Ctor.mk …` form too.
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

/-- Whether the written identifier `ident` denotes the fully-qualified `name`. -/
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

/-- Edit 2: rewrite a self-recursive call `funcSim a₁ … aₙ` to `funcImpl (explode a₁) … (explode aₙ)`, where a split-type argument `aᵢ` is exploded into its field accessors (`ctx ↦ ctx.buf ctx.spec ctx.sim`). -/
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

/-- Project a result leaf onto the impl field. -/
private meta def projectLeaf (field0? : Option Name) (stx : Term) : MacroM Term := do
  match field0? with
  | none        => pure stx
  | some field0 => `($stx.$(mkIdent field0):ident)

mutual
/-- Project the tail of a `doSeq` (the last `doSeqItem`): a terminal `doExpr` is projected as a term; `doIf`/`doMatch` recurse into their branch sequences; binding items (`let`, `←`) are left alone. -/
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
    -- `match`: project each alternative's right-hand side (the alternatives node is `match`'s last child; each `matchAlt`'s rhs is its last child).
    if stx.raw.isOfKind ``Parser.Term.match then
      let altsIdx := stx.raw.getNumArgs - 1
      let altsNode := stx.raw[altsIdx]
      let alts' ← altsNode[0].getArgs.mapM fun alt => do
        let rhsIdx := alt.getNumArgs - 1
        let rhs' ← projectResultTail implName field0? ⟨alt[rhsIdx]⟩
        pure (alt.setArg rhsIdx rhs')
      let altsNode' := altsNode.setArg 0 (altsNode[0].setArgs alts')
      return ⟨stx.raw.setArg altsIdx altsNode'⟩
    -- `do` block: descend into its `doSeq` tail.
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

/-- The field-0 accessor name (`buf`/`impl`) of `funcSim`'s return split type, for result projection. -/
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

/-- Prepend the structured-rebinding `let`s (edit 1) so the verbatim-copied body sees its original parameters: `let ctx := ⟨ctx_buf, GHOST_ctx_spec, ctx_sim⟩` for each split parameter `ctx`. -/
private meta def prependRebindLets (plans : Array ParamPlan) (body : Term) : MacroM Term := do
  let mut body := body
  for plan in plans.reverse do
    if let some structType := plan.structType? then
      -- `let ctx : Sim.IRContext OpInfo := ⟨ctx_buf, GHOST_ctx_spec, ctx_sim⟩`; the ascription lets the anonymous constructor pick the right structure.
      let structType' : Term := ⟨← substSplitIdents plans structType⟩
      let fields := plan.implFieldNames.map (mkIdent ·)
      let lhs := mkIdent plan.userName
      body ← `(let $lhs:ident : $structType' := ⟨$fields,*⟩
               $body)
  return body

end Veir.Buffed

open Lean Elab Command Veir.Buffed

/-- `<modifiers> buffed def fooSim … := …` elaborates the `Sim`-level definition, then generates `fooImpl`, `fooSpec`, and the non-suffixed base wrapper from it. -/
syntax (name := buffedCmd)
  declModifiers "buffed"
    (atomic(ppSpace "(" &"inline") " := " (&"true" <|> &"false") ")")?
    (atomic(ppSpace "(" &"def_lemma") " := " (&"true" <|> &"false") ")")? ppSpace
    Parser.Command.definition : command

/-- Prepend `@[inline]` to a definition's `declModifiers`, the same way one would write `@[inline] def …` in source. -/
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

/-- Build the recursive `<name>Impl` as a fresh `def`: reuse the impl signature from `buildBuffedImpl`, and rewrite `funcSim`'s source body with the three edits (rebind split params, self-call → `<name>Impl` with exploded args, project the result). -/
private meta def buildRecursiveImplCmd (declName implName : Name) (inline : Bool) (defn : Syntax)
    : CommandElabM (TSyntax `command) := do
  let plans ← liftCoreM <| MetaM.run' (Veir.Buffed.buffedParamPlan declName)
  let (binders, retTy) ← buffedImplSig declName plans defn
  let field0? ← liftCoreM <| MetaM.run' (buffedReturnField0 declName)
  -- `defn` = `def declId optDeclSig declVal …`; the body is `declVal[1]` of a `declValSimple`, whose trailing `where`/`termination_by`/`decreasing_by` we keep by rewriting only `[1]`.
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
    -- `Sim` declarations are always inline.
    let mods ← prependInlineModifier mods
    -- Re-attach the modifiers to the bare `def` and elaborate the user's `Sim` definition as written.
    let cmd ← `($mods:declModifiers $defn:definition)
    elabCommand cmd
    -- Recover the declaration name from the `declId` and qualify it with the current namespace.
    let some declId := cmd.raw.find? (·.getKind == ``Parser.Command.declId)
      | throwError "buffed: could not find the definition's name"
    let declName := (← getCurrNamespace) ++ declId[0].getId
    -- Detect recursion from the *source* body (the elaborated value compiles self-calls into `brecOn`/`WellFounded.fix`, hiding the literal self-reference).
    let body := defn.raw[3][1]
    if mentionsCall declName body then
      -- Recursive: emit a genuinely recursive `<name>Impl`, then spec + base from the Sim term.
      let implName := Veir.Buffed.mkImplName declName
      unless (← getEnv).contains implName do
        elabCommand (← buildRecursiveImplCmd declName implName inline defn.raw)
      -- Emit the `<name>_impl` lemma `(funcSim args).impl = funcImpl (projected args)`, proved by induction along `<name>Sim` (see `mkRecursiveImplLemmaProof`).
      if defLemma then
        liftCoreM <| generateBuffedImplLemma declName (recursive := true)
      liftCoreM <| generateBuffedSpecAndBase declName (recursive := true) (defLemma := defLemma)
      -- Emit the `<name>_def` lemma `<base> args = <name>Sim args` by induction along `<name>Sim`, e.g. the hand-written `Rewriter.detachOperands.loop_def`.
      if defLemma then
        liftCoreM <| generateBuffedDefLemma declName (recursive := true)
    else
      liftCoreM <| generateBuffed declName inline (defLemma := defLemma)

initialize registerTraceClass `Buffed.ghosting (inherited := false)
initialize registerTraceClass `Buffed.ghosting.defs (inherited := false)
