module

public import Veir.Buffered.IR.Buffed.SimDefs
public import Lean

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
  -- Match auxiliaries may be private; do not force-expose their callers.
  let expose := (info.type.getUsedConstants ++ info.value.getUsedConstants).all (!isPrivateName ·)
  let decl := Declaration.defnDecl info
  addDecl decl (forceExpose := expose)
  if let some userName := privateToUserName? info.name then
    modifyEnv fun env => addAlias env userName info.name
  setInline info.name inline
  compileDecl decl

private meta def generate (name : Name) (inlineInner : Bool) : MetaM Unit := do
  let info ← getConstInfoDefn name
  unless info.safety == .safe do
    throwError "buffed: expected a safe definition"
  let base ← baseName name
  let .str parent last := base | unreachable!
  let inner := .str parent (last ++ "Inner")
  let unfoldName := base ++ `unfold
  for generated in #[inner, base, unfoldName] do
    if (← getEnv).contains generated then
      throwError "buffed: declaration already exists: {generated}"
  let (type, value) ← innerDefinition info
  addDefinition { info with name := inner, type, value, hints := .regular 0, all := [inner] } inlineInner
  let levels := info.levelParams.map Level.param
  let wrapper ← forallTelescope info.type fun xs _ => do
    mkLambdaFVars xs (mkAppN (mkConst inner levels) (← projectedArgs xs))
  addDefinition { info with name := base, value := wrapper, hints := .regular 0, all := [base] } true
  if isProtected (← getEnv) name then
    modifyEnv fun env => addProtected (addProtected env base) inner
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
`fooSim` and `foo` are always inline. `inline := false` makes `fooInner` noinline;
the default is `true`, matching the original `buffed` command. Ordinary arrays,
options, and return types are left untouched. -/
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
    let inlineInner := flag?.all (·.raw.getKind != `token.false)
    liftTermElabM <| Veir.Buffered.Buffed.generate name inlineInner
