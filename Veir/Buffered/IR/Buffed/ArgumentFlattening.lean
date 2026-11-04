module

public import Veir.Buffered.IR.Buffed.SimDefs
public import Veir.Buffered.IR.Buffed.ArgumentFlatteningLemmas
public import Lean
import all Init.Internal.Order.Basic

/-!
`buffed def fooSim ... := ...` introduces an argument-flattened `fooInner` and an
inline wrapper `foo`. This is only a calling-convention transformation: every field,
including `Erased` specifications and dependent proofs, is passed unchanged. Results
are neither projected nor reconstructed. No specification function is generated.
-/

open Lean Meta Elab Command

namespace Veir.Buffered.Buffed

private meta def splitTypes : Array Name := #[
  ``Sim.IRContext, ``Sim.RawIRContext,
  ``Sim.OperationPtr, ``Sim.OptionOperationPtr,
  ``Sim.BlockPtr, ``Sim.OptionBlockPtr,
  ``Sim.RegionPtr, ``Sim.OptionRegionPtr,
  ``Sim.OpResultPtr, ``Sim.OptionOpResultPtr,
  ``Sim.BlockArgumentPtr, ``Sim.OptionBlockArgumentPtr,
  ``Sim.OpOperandPtr, ``Sim.OptionOpOperandPtr,
  ``Sim.BlockOperandPtr, ``Sim.OptionBlockOperandPtr,
  ``Sim.ValuePtr, ``Sim.OptionValuePtr,
  ``Sim.OpOperandPtrPtr, ``Sim.BlockOperandPtrPtr,
  ``Sim.GenericPtr, ``Sim.OptionGenericPtr]

private meta def splitInfo? (type : Expr) : MetaM (Option (Expr × StructureInfo)) := do
  let type ← whnf type
  if splitTypes.contains (type.getAppFn.constName?.getD .anonymous) then
    return (getStructureInfo? (← getEnv) type.getAppFn.constName!).map (type, ·)
  return none

private meta def baseName (name : Name) : CoreM Name := do
  let .str parent last := name
    | throwError "buffed: expected a definition with a `Sim` suffix"
  unless last.endsWith "Sim" && last.length > 3 do
    throwError "buffed: expected a definition with a `Sim` suffix"
  return .str parent (last.dropEnd 3).toString

/-- Thread substitutions through later binders, including types and proof arguments
that depend on an earlier context or pointer. Constructor fields are processed in
order for the same reason (in particular `IRContext.sim` depends on both fields). -/
private meta def innerDefinition (info : DefinitionVal) : MetaM (Expr × Expr) := do
  forallTelescope info.type fun xs _ => do
    let rec go (remaining : List Expr) (old replacements locals : Array Expr) :
        MetaM (Expr × Expr) := do
      match remaining with
      | [] =>
        let body := mkAppN (mkConst info.name (info.levelParams.map Level.param)) replacements
        return (← mkForallFVars locals (← inferType body), ← mkLambdaFVars locals body)
      | x :: rest =>
        let decl ← x.fvarId!.getDecl
        let type := decl.type.replaceFVars old replacements
        match ← splitInfo? type with
        | none =>
          withLocalDecl decl.userName decl.binderInfo type fun y =>
            go rest (old.push x) (replacements.push y) (locals.push y)
        | some (structType, _) =>
          let inductiveInfo ← getConstInfoInduct structType.getAppFn.constName!
          let ctor := mkAppN
            (mkConst inductiveInfo.ctors.head! structType.getAppFn.constLevels!) structType.getAppArgs
          forallTelescope (← inferType ctor) fun fields _ => do
            let rec introduce (i : Nat) (newFields : Array Expr) : MetaM (Expr × Expr) := do
              if h : i < fields.size then
                let field ← fields[i].fvarId!.getDecl
                let fieldType := field.type.replaceFVars (fields.extract 0 i) newFields
                let name := Name.mkSimple s!"{decl.userName}_{field.userName}"
                withLocalDecl name .default fieldType fun y =>
                  introduce (i + 1) (newFields.push y)
              else
                go rest (old.push x) (replacements.push (mkAppN ctor newFields))
                  (locals ++ newFields)
            introduce 0 #[]
    go xs.toList #[] #[] #[]

private meta def projectedArgs (xs : Array Expr) : MetaM (Array Expr) := do
  let mut args := #[]
  for x in xs do
    match ← splitInfo? (← inferType x) with
    | none => args := args.push x
    | some (type, info) =>
      for i in [:info.fieldNames.size] do
        args := args.push (mkProj type.getAppFn.constName! i x)
  return args

private meta def setInline (name : Name) (inline : Bool) : CoreM Unit := do
  let attr := if inline then `inline else `noinline
  let stx := Syntax.node .none ``Lean.Parser.Attr.simple
    #[mkIdent attr, Syntax.node .none nullKind #[]]
  Attribute.add name attr stx .global

private meta def addDefinition (info : DefinitionVal) (inline : Bool) : MetaM Unit := do
  -- Use Lean's normal heights: unfold the adapter before its (possibly large,
  -- recursive) callee during definitional-equality checks.
  let info := { info with hints := .regular (getMaxHeight (← getEnv) info.value + 1) }
  -- Match auxiliaries may be private; do not force-expose their callers.
  let expose := (info.type.getUsedConstants ++ info.value.getUsedConstants).all (!isPrivateName ·)
  let decl := Declaration.defnDecl info
  addDecl decl (forceExpose := expose)
  if let some userName := privateToUserName? info.name then
    modifyEnv fun env => addAlias env userName info.name
  setInline info.name inline
  compileDecl decl

syntax (name := recursiveCall) "buffed_recur% " "(" term ")" "(" term ")" : term

private meta partial def qualifyRecursiveHead (name : Name) (s : Syntax) : MetaM Syntax := do
  if s.isIdent then
    if ((← getLCtx).findFromUserName? s.getId).isSome then return s
    return mkIdentFrom s (`_root_ ++ name)
  else if s.isOfKind ``Parser.Term.app then
    return s.setArg 0 (← qualifyRecursiveHead name s[0])
  else if s.isOfKind ``Parser.Term.explicit || s.isOfKind ``Parser.Term.paren then
    return s.setArg 1 (← qualifyRecursiveHead name s[1])
  else return s

/-- Elaborate source arguments first, then project them in the elaborated term.
This preserves implicit/named/default arguments without hiding recursive calls
behind a forwarding lambda from the termination checker. -/
@[term_elab recursiveCall]
public meta def elabRecursiveCall : Term.TermElab := fun stx expectedType? => do
    let source : Term := ⟨stx[2]⟩
    let inner : Term := ⟨stx[5]⟩
    let .str parent last := inner.raw.getId
      | throwError "buffed: invalid recursive target"
    let original := .str parent ((last.dropEnd 5).toString ++ "Sim")
    -- The original declaration's temporary recursive-name alias is no longer in scope.
    let source : Term := ⟨← qualifyRecursiveHead original source⟩
    let e ← Term.elabTerm source expectedType?
    Term.synthesizeSyntheticMVarsNoPostponing
    let e := (← instantiateMVars e).consumeMData
    -- A locally shadowed name is not a recursive reference.
    unless e.getAppFn.consumeMData.isConstOf original do return e
    let targetId := mkIdent (privateToUserName inner.raw.getId)
    let target := (← Term.elabTerm (← `(@$targetId)) none).consumeMData
    let value ← forallTelescope (← inferType e) fun more _ => do
      let e := mkAppN e more
      let args ← projectedArgs e.getAppArgs
      mkLambdaFVars more (mkAppN target args)
    return value

/-- Delaborate generated signatures without turning projections into receiver syntax. -/
private meta def syntaxOf (e : Expr) : MetaM Term :=
  withOptions (fun o => o.setBool `pp.fieldNotation false |>.setBool `pp.funBinderTypes true) <|
    PrettyPrinter.delab e

private meta def selfIdent (name id : Name) : Bool :=
  let id := id.eraseMacroScopes
  name == id || (`_root_ ++ name) == id || name.toString.endsWith s!".{id}"

private meta partial def callHead? (s : Syntax) : Option Name :=
  if s.isIdent then some s.getId
  else if s.isOfKind ``Parser.Term.app then callHead? s[0]
  else if s.isOfKind ``Parser.Term.explicit || s.isOfKind ``Parser.Term.paren then callHead? s[1]
  else none

private meta partial def replaceSelf (name inner : Name) (stx : Syntax) : MetaM Syntax := do
  let stx := stx.setArgs (← stx.getArgs.mapM (replaceSelf name inner))
  if stx.isOfKind ``Parser.Term.app && (callHead? stx[0]).any (selfIdent name) then
    let source : Term := ⟨stx⟩
    let target := mkIdent inner
    return (← `(buffed_recur% ($source) ($target))).raw
  return stx

private meta partial def substRebindings (substitutions : Array (Name × Term))
    (s : Syntax) : MetaM Syntax := do
  if s.isIdent then
    let parts := s.getId.eraseMacroScopes.components
    if let some first := parts.head? then
      if let some (_, value) := substitutions.find? (·.1 == first) then
        let rest := parts.tail.foldl (· ++ ·) Name.anonymous
        if rest.isAnonymous then return value
        return (← `($value.$(mkIdent rest):ident)).raw
  return s.setArgs (← s.getArgs.mapM (substRebindings substitutions))

private meta def recursiveCommand (name inner : Name) (inlineInner : Bool)
    (defn : Syntax) : MetaM (TSyntax `command) := do
  let info ← getConstInfoDefn name
  let (innerType, _) ← innerDefinition info
  let levels := info.levelParams.map Level.param
  let (binders, ret) ← forallTelescope innerType fun xs ret => do
    let binders ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      let id := mkIdent d.userName
      let ty ← syntaxOf d.type
      match d.binderInfo with
      | .default => `(Parser.Term.bracketedBinderF| ($id : $ty))
      | .implicit => `(Parser.Term.bracketedBinderF| {$id : $ty})
      | .strictImplicit => `(Parser.Term.bracketedBinderF| ⦃$id : $ty⦄)
      | .instImplicit => `(Parser.Term.bracketedBinderF| [$id : $ty])
    return (binders, ← syntaxOf ret)
  let (rebindings, substitutions) ← forallTelescope info.type fun xs _ => do
    let mut rebindings : Array (Ident × Term × Term) := #[]
    let mut substitutions : Array (Name × Term) := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if let some (ty, sInfo) ← splitInfo? d.type then
        let fields := sInfo.fieldNames.map fun field => mkIdent (.mkSimple s!"{d.userName}_{field}")
        let value ← `(⟨$fields,*⟩)
        let type ← syntaxOf ty
        rebindings := rebindings.push (mkIdent d.userName, type, value)
        let typed ← `(($value : $type))
        substitutions := substitutions.push (d.userName, typed)
    return (rebindings, substitutions)
  let mut body : Term := ⟨← replaceSelf name inner defn[3][1]⟩
  for (id, ty, value) in rebindings.reverse do
    body ← `(let $id : $ty := $value; $body)
  -- The termination measure lives outside the body's rebinding lets.
  let suffix ← substRebindings substitutions defn[3][2]
  let value : TSyntax ``Parser.Command.declVal := ⟨defn[3].setArg 1 body |>.setArg 2 suffix⟩
  let id := mkIdent (`_root_ ++ privateToUserName inner)
  let declId ← if levels.isEmpty then `(Parser.Command.declId| $id)
    else `(Parser.Command.declId| $id.{$(info.levelParams.toArray.map mkIdent),*})
  let attr := mkIdent (if inlineInner then `inline else `noinline)
  if isPrivateName inner then
    `(@[$attr:ident] private def $declId $binders* : $ret $value:declVal)
  else
    `(@[$attr:ident] def $declId $binders* : $ret $value:declVal)

/-- Admissibility of evaluating a dependent curried function at fixed arguments. -/
private meta partial def admissibleApplication (type inst : Expr) (args : List Expr)
    (predicate proof : Expr) : MetaM Expr := do
  match args with
  | [] => return proof
  | arg :: rest =>
    let type ← whnf type
    let next := type.bindingBody!.instantiate1 arg
    let inst := inst.headBeta
    unless inst.isAppOf ``Lean.Order.instCCPOPi do
      throwError "buffed: expected pointwise fixed-point order, got {inst}"
    let instArgs := inst.getAppArgs
    let proof ← admissibleApplication next (mkApp instArgs[2]! arg) rest predicate proof
    let predicate ← withLocalDeclD `g next fun g =>
      mkLambdaFVars #[g] (mkApp predicate (mkAppN g rest.toArray))
    mkAppOptM ``admissible_eval ((instArgs ++ #[arg, predicate, proof]).map some)

private meta def unfoldFix (name : Name) (args : Array Expr) : MetaM (Expr × Expr) := do
  let some info := PartialFixpoint.eqnInfoExt.find? (← getEnv) name
    | throwError "buffed: missing fixed-point metadata for {name}"
  let value ← deltaExpand (mkAppN (mkConst name (info.levelParams.map Level.param)) args)
    (fun n => n == name || n == info.declNameNonRec)
  let some call := value.find? (fun e => e.isAppOf ``Lean.Order.fix && e.getAppNumArgs >= 4)
    | throwError "buffed: unsupported fixed-point representation for {name}: {value}"
  return (value, call)

/-- Reindex the original least fixed point. This also handles fields that become
fixed parameters after splitting, without assuming termination or inventing specs. -/
private meta def partialEquality (name inner : Name) (xs : Array Expr) : MetaM Expr := do
  let (sourceValue, sourceCall) ← unfoldFix name xs
  let (innerValue, innerCall) ← unfoldFix inner (← projectedArgs xs)
  let sourceArgs := sourceCall.getAppArgs
  let innerArgs := innerCall.getAppArgs
  let innerFix := mkAppN innerCall.getAppFn (innerArgs.extract 0 4)
  let a := sourceArgs[0]!
  let b := innerArgs[0]!
  let reindex ← withLocalDeclD `f a fun f =>
    forallTelescope b fun ys _ => do
      let replacements := (innerArgs.extract 4 innerArgs.size).zip ys
      let args ← (sourceArgs.extract 4 sourceArgs.size).mapM fun arg => do
        let arg ← match ← splitInfo? (← inferType arg) with
          | none => pure arg
          | some (ty, structInfo) => do
            let ctor := (← getConstInfoInduct ty.getAppFn.constName!).ctors.head!
            pure <| mkAppN (mkConst ctor ty.getAppFn.constLevels!)
              (ty.getAppArgs ++ structInfo.fieldNames.mapIdx (fun i _ => mkProj ty.getAppFn.constName! i arg))
        pure <| arg.replace fun e => (replacements.find? (·.1 == e)).map (·.2)
      mkLambdaFVars #[f] (← mkLambdaFVars ys (mkAppN f args))
  let hadm ← withLocalDeclD `bound b fun bound =>
    forallTelescope b fun args type => do
      let mut resultInst := innerArgs[1]!
      for arg in args do
        resultInst := (mkApp resultInst.headBeta.getAppArgs[2]! arg).headBeta
      let order ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[some type, some resultInst]
      let predicate ← withLocalDeclD `v type fun v => do
        mkLambdaFVars #[v] (← mkAppOptM ``Lean.Order.PartialOrder.rel (#[type, order, v, mkAppN bound args].map some))
      let h ← mkAppOptM ``admissible_upper (#[type, resultInst, mkAppN bound args].map some)
      let sourceInputs ← withLocalDeclD `f a fun f => do
        let value := (mkAppN (mkApp reindex f) args).headBeta
        pure value.getAppArgs
      let mut h ← admissibleApplication a sourceArgs[1]! sourceInputs.toList predicate h
      for arg in args.reverse do
        h ← mkAppOptM ``Lean.Order.admissible_pi #[some a, some sourceArgs[1]!, none, none, some (← mkLambdaFVars #[arg] h)]
      mkLambdaFVars #[bound] h
  let commute ← withLocalDeclD `f a fun f => do
    let lhs := mkApp reindex (mkApp sourceArgs[2]! f)
    let rhs := mkApp innerArgs[2]! (mkApp reindex f)
    unless ← withTransparency .reducible <| isDefEq lhs rhs do
      throwError "buffed: recursive fixed-point bodies do not commute for {name}"
    mkLambdaFVars #[f] (← mkEqRefl lhs)
  let fusion ← mkAppOptM ``reindex_fix
    (#[a, b, sourceArgs[1]!, innerArgs[1]!, sourceArgs[2]!, innerArgs[2]!, sourceArgs[3]!, innerArgs[3]!, reindex].map some)
  -- Avoid eager default-transparency unification of these proof arguments: it
  -- unfolds unrelated large callees while comparing beta/eta-equivalent steps.
  -- The completed theorem application is checked by the kernel in `addDecl`.
  let equality := mkApp2 fusion hadm commute
  let view ← withLocalDeclD `g b fun g =>
    mkLambdaFVars #[g] (innerValue.replace fun e => if e == innerFix then some g else none)
  let equality ← withTransparency .reducible <| mkAppM ``congrArg #[view, equality]
  let expected ← mkEq sourceValue innerValue
  unless ← withTransparency .reducible <| isDefEq (← inferType equality) expected do
    throwError "buffed: fixed-point reindexing did not recover the original application for {name}"
  mkEqSymm equality

/-- Contract reconstructed inputs before matching induction hypotheses. Native
projections and proof fields otherwise obstruct syntactic simp/match indexing.
Every contraction is checked by definitional equality. -/
private meta def normalizeSimEta (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun e => do
    let .const name _ := e.getAppFn | return .continue
    let some (.ctorInfo ci) := (← getEnv).find? name | return .continue
    unless splitTypes.contains ci.induct && e.getAppNumArgs == ci.numParams + ci.numFields do
      return .continue
    let field := e.getAppArgs[ci.numParams]!.consumeMData
    let candidate ← match field with
      | .proj _ 0 x => pure (some x)
      | _ => do
        let .const name _ := field.getAppFn | pure none
        let some pi ← getProjectionFnInfo? name | pure none
        if pi.i == 0 then pure (some field.appArg!) else pure none
    let some x := candidate | return .continue
    if ← isDefEq e x then return .done x else return .continue)

private meta def generate (name : Name) (inlineInner : Bool) (recursive := false) : MetaM Unit := do
  let info ← getConstInfoDefn name
  unless info.safety == .safe do
    throwError "buffed: expected a safe definition"
  let base ← baseName name
  let .str parent last := base | unreachable!
  let inner := .str parent (last ++ "Inner")
  let unfoldName := base ++ `unfold
  for generated in (if recursive then #[base, unfoldName] else #[inner, base, unfoldName]) do
    if (← getEnv).contains generated then
      throwError "buffed: declaration already exists: {generated}"
  unless recursive do
    let (type, value) ← innerDefinition info
    addDefinition { info with name := inner, type, value, all := [inner] } inlineInner
  let levels := info.levelParams.map Level.param
  let wrapper ← forallTelescope info.type fun xs _ => do
    mkLambdaFVars xs (mkAppN (mkConst inner levels) (← projectedArgs xs))
  addDefinition { info with name := base, value := wrapper, all := [base] } true
  if isProtected (← getEnv) name then
    modifyEnv fun env => addProtected (addProtected env base) inner
  let equality ← forallTelescope info.type fun xs _ => do
    if !recursive then
      return ← mkLambdaFVars xs (← mkEqRefl (mkAppN (mkConst name levels) xs))
    if (PartialFixpoint.eqnInfoExt.find? (← getEnv) name).isSome then
      return ← mkLambdaFVars xs (← partialEquality name inner xs)
    let goal ← mkForallFVars xs (← mkEq (mkAppN (mkConst inner levels) (← projectedArgs xs)) (mkAppN (mkConst name levels) xs))
    let proof ← mkFreshExprSyntheticOpaqueMVar goal
    let goals ← (Elab.Tactic.run proof.mvarId! do
      Elab.Tactic.evalTactic (← `(tactic| intros))
      Elab.Tactic.evalTactic (← `(tactic| fun_induction $(mkIdent name)))
      Elab.Tactic.evalTactic (← `(tactic| all_goals (conv => lhs; unfold $(mkIdent inner))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals (try dsimp only at *)))
      let goals ← (← Elab.Tactic.getGoals).mapM fun g => g.withContext do
        g.replaceTargetDefEq (← normalizeSimEta (← g.getType))
      Elab.Tactic.setGoals goals
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try simp_all (config := { zetaDelta := true }) only); (try with_reducible assumption); (try with_reducible rfl))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try simp_all (config := { zetaDelta := true })); (try with_reducible assumption); (try with_reducible rfl); (try grind))))
      ).run' { errToSorry := false }
    unless goals.isEmpty do throwError "buffed: could not prove recursive argument equivalence for {name}\n{goals}"
    let proof ← instantiateMVars proof
    return proof
  if equality.hasSyntheticSorry ||
      (equality.hasNonSyntheticSorry && !(← collectAxioms name).contains ``sorryAx) then
    throwError "buffed: invalid recursive equivalence proof for {name}"
  let eqName := base ++ `eq_sim
  let equalityType ← forallTelescope info.type fun xs _ => do
    mkForallFVars xs (← mkEq (mkAppN (mkConst base levels) xs) (mkAppN (mkConst name levels) xs))
  addDecl (.thmDecl { name := eqName, levelParams := info.levelParams, type := equalityType, value := equality })
  let equation? ← getUnfoldEqnFor? name (nonRec := true)
  forallTelescope info.type fun xs _ => do
    let lhs := mkAppN (mkConst base levels) xs
    -- Use the original unfolding equation when available, so recursion unfolds
    -- to a source-level match rather than an implementation using `brecOn`/`fix`.
    let (rhs, proof) ← match equation? with
      | some equation => do
        let proof := mkAppN (mkConst equation levels) xs
        let some (_, _, rhs) := (← whnf (← inferType proof)).eq?
          | throwError "buffed: expected an equality from {equation}"
        pure (rhs, proof)
      | none => do
        let rhs := info.value.beta xs
        pure (rhs, ← mkEqRefl rhs)
    -- Equations for non-exposed definitions can mention private match helpers.
    -- Expand these definitionally in the statement so the exported theorem is
    -- usable without `import all`; its proof still uses the original equation.
    let env ← getEnv
    let expandPrivate := fun n => isPrivateName n && match env.find? n with
      | some (.defnInfo _) | some (.thmInfo _) => true
      | _ => false
    -- Proof auxiliaries can also be private. Expanding their checked proof terms
    -- is valid by proof irrelevance; never unfold opaque computational values.
    let rhs ← deltaExpand rhs expandPrivate (allowOpaque := true)
    unless isPrivateName base do
      for n in rhs.getUsedConstants do
        if isPrivateName n && ((env.setExporting true).find? n).isNone then
          throwError "buffed: cannot export unfolding equation; non-exported constant {privateToUserName n}"
    let type ← mkForallFVars xs (← mkEq lhs rhs)
    let proof ← mkEqTrans (mkAppN (mkConst eqName levels) xs) proof
    let value ← mkLambdaFVars xs proof
    addDecl (.thmDecl { name := unfoldName, levelParams := info.levelParams, type, value })
    if let some userName := privateToUserName? unfoldName then
      modifyEnv fun env => addAlias env userName unfoldName
    -- Provide the conventional equation names for clients that request them.
    -- Tactics that delta-reduce the wrapper itself can still expose `fooInner`;
    -- explicit proof rewriting should therefore use `foo.unfold`.
    for suffix in [eqn1ThmSuffix, unfoldThmSuffix] do
      let equationName := mkEqLikeNameFor (← getEnv) base suffix
      addDecl (.thmDecl { name := equationName, levelParams := info.levelParams, type := type, value := mkConst unfoldName levels })
      if let some userName := privateToUserName? equationName then
        modifyEnv fun env => addAlias env userName equationName

/-- Add inline before elaboration/compilation, rather than changing it after the
compiler has already processed the original definition. -/
private meta def inlineModifiers (mods : TSyntax ``Parser.Command.declModifiers) :
    CommandElabM (TSyntax ``Parser.Command.declModifiers) := do
  let attr ← `(Parser.Term.attrInstance| $(mkIdent `inline):ident)
  let raw := mods.raw
  let attrs := raw[1]
  if attrs.getNumArgs == 0 then
    let attrs ← `(Parser.Term.attributes| @[$attr:attrInstance])
    return ⟨raw.setArg 1 (mkNullNode #[attrs.raw])⟩
  else
    let node := attrs[0]
    let list := node[1]
    let list := list.setArgs (#[attr.raw, mkNullNode #[]] ++ list.getArgs)
    return ⟨raw.setArg 1 (mkNullNode #[node.setArg 1 list])⟩

end Veir.Buffered.Buffed

/-- Generate `fooInner`, `foo`, and `foo.unfold` from `fooSim`.
`fooSim` and `foo` are always inline. Recursive `fooInner` definitions are always
noinline, including `partial_fixpoint`, so Lean specializes their bodies rather than
treating them as inline templates. For nonrecursive inners, `inline := false` makes
`fooInner` noinline; the default is `true`. Ordinary arrays, options, and return types
are left untouched. -/
syntax (name := buffedCmd)
  declModifiers "buffed"
    (atomic(ppSpace "(" &"inline" " := " (&"true" <|> &"false") ")"))? ppSpace
    Parser.Command.definition : command

elab_rules : command
  | `($mods:declModifiers buffed $[(inline := $flag?)]? $defn:definition) => do
    let mods ← Veir.Buffered.Buffed.inlineModifiers mods
    let cmd ← `($mods:declModifiers $defn:definition)
    elabCommand cmd
    let some id := defn.raw.find? (·.getKind == ``Parser.Command.declId)
      | throwError "buffed: could not find the definition's name"
    let name ← liftCoreM <| resolveGlobalConstNoOverload id[0]
    let requestedInline := flag?.all (·.raw.getKind != `token.false)
    let recursive ← liftTermElabM do
      let info ← getConstInfoDefn name
      unless info.safety == .safe do throwError "buffed: expected a safe definition"
      return (← isRecursiveDefinition name) || (PartialFixpoint.eqnInfoExt.find? (← getEnv) name).isSome
    -- Recursive inline templates skip specialization without being inlined. Set
    -- the effective policy before elaborating/compiling the rewritten body.
    let inlineInner := requestedInline && !recursive
    if recursive then
      let base ← liftCoreM <| Veir.Buffered.Buffed.baseName name
      let .str parent last := base | throwError "buffed: invalid name"
      let inner := .str parent (last ++ "Inner")
      let cmd ← liftTermElabM <| Veir.Buffered.Buffed.recursiveCommand name inner inlineInner defn
      elabCommand cmd
    liftTermElabM <| Veir.Buffered.Buffed.generate name inlineInner recursive
