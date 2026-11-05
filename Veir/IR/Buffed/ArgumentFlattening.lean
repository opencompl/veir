module

public import Veir.IR.Buffed.SimDefs
public import Lean

/-!
`buffed` is a compatibility command for the declarations that historically used the
buffered argument-flattening generator.  It no longer changes argument or result
representations. The requested `inline` setting is forwarded to the source and public
definitions; the latter remains a transparent wrapper with the original signature.

The `foo.eq_sim` and `foo.unfold` theorems are retained so existing proofs do not have
to know that the optimization has been removed.
-/

open Lean Meta Elab Command

namespace Veir.Buffed

private meta def baseName (name : Name) : CoreM Name := do
  let .str parent last := name
    | throwError "buffed: expected a definition with a `Sim` suffix"
  unless last.endsWith "Sim" && last.length > 3 do
    throwError "buffed: expected a definition with a `Sim` suffix"
  return .str parent (last.dropEnd 3).toString

private meta def setInline (name : Name) (inline : Bool) : CoreM Unit := do
  let attr := if inline then `inline else `noinline
  let stx := Syntax.node .none ``Lean.Parser.Attr.simple
    #[mkIdent attr, Syntax.node .none nullKind #[]]
  Attribute.add name attr stx .global

/-- Structure eta-expansion is definitionally the identity. It only keeps dependent
implicit arguments inferable from the result of the compatibility wrapper. -/
private meta def etaStructure (value : Expr) : MetaM Expr := do
  let type ← whnf (← inferType value)
  let some typeName := type.getAppFn.constName? | return value
  let some structInfo := getStructureInfo? (← getEnv) typeName | return value
  let ctorName := (← getConstInfoInduct typeName).ctors.head!
  let mut result := mkAppN (mkConst ctorName type.getAppFn.constLevels!) type.getAppArgs
  for i in [:structInfo.fieldNames.size] do
    result := mkApp result (mkProj typeName i value)
  return result

private meta def addDefinition (info : DefinitionVal) (inline : Bool) : MetaM Unit := do
  let info := { info with hints := .regular (getMaxHeight (← getEnv) info.value + 1) }
  let expose := (info.type.getUsedConstants ++ info.value.getUsedConstants).all (!isPrivateName ·)
  let decl := Declaration.defnDecl info
  addDecl decl (forceExpose := expose)
  if let some userName := privateToUserName? info.name then
    modifyEnv fun env => addAlias env userName info.name
  setInline info.name inline
  compileDecl decl

/-- Add a compiler annotation before Lean elaborates and compiles a definition. -/
private meta def inlineModifiers (mods : TSyntax ``Parser.Command.declModifiers)
    (inline : Bool) : CommandElabM (TSyntax ``Parser.Command.declModifiers) := do
  let attrName := if inline then `inline else `noinline
  let attr ← `(Parser.Term.attrInstance| $(mkIdent attrName):ident)
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

/-- Retain the old public names and proof interface, but do not flatten anything. -/
private meta def generateForwarder (source : Name) (inline : Bool) : MetaM Unit := do
  let info ← getConstInfoDefn source
  let base ← baseName source
  for generated in #[base, base ++ `unfold, base ++ `eq_sim] do
    if (← getEnv).contains generated then
      throwError "buffed: declaration already exists: {generated}"

  let levels := info.levelParams.map Level.param
  let wrapper ← forallTelescope info.type fun xs _ => do
    let sourceCall := mkAppN (mkConst source levels) xs
    mkLambdaFVars xs (← etaStructure sourceCall)
  addDefinition { info with name := base, value := wrapper, all := [base] } inline

  if isProtected (← getEnv) source then
    modifyEnv fun env => addProtected env base

  let eqName := base ++ `eq_sim
  let equalityType ← forallTelescope info.type fun xs _ => do
    mkForallFVars xs (← mkEq (mkAppN (mkConst base levels) xs)
      (mkAppN (mkConst source levels) xs))
  let equality ← forallTelescope info.type fun xs _ => do
    mkLambdaFVars xs (← mkEqRefl (mkAppN (mkConst source levels) xs))
  addDecl (.thmDecl {
    name := eqName
    levelParams := info.levelParams
    type := equalityType
    value := equality
  })
  if let some userName := privateToUserName? eqName then
    modifyEnv fun env => addAlias env userName eqName

  let unfoldName := base ++ `unfold
  let equation? ← getUnfoldEqnFor? source (nonRec := true)
  forallTelescope info.type fun xs _ => do
    let lhs := mkAppN (mkConst base levels) xs
    let (rhs, sourceProof) ← match equation? with
      | some equation => do
        let proof := mkAppN (mkConst equation levels) xs
        let some (_, _, rhs) := (← whnf (← inferType proof)).eq?
          | throwError "buffed: expected an equality from {equation}"
        pure (rhs, proof)
      | none => do
        let rhs := info.value.beta xs
        pure (rhs, ← mkEqRefl rhs)

    -- Public compatibility theorems must not expose private match/proof helpers.
    let env ← getEnv
    let expandPrivate := fun n => isPrivateName n && match env.find? n with
      | some (.defnInfo _) | some (.thmInfo _) => true
      | _ => false
    let rhs ← deltaExpand rhs expandPrivate (allowOpaque := true)
    unless isPrivateName base do
      for n in rhs.getUsedConstants do
        if isPrivateName n && ((env.setExporting true).find? n).isNone then
          throwError "buffed: cannot export unfolding equation; non-exported constant {privateToUserName n}"

    let type ← mkForallFVars xs (← mkEq lhs rhs)
    let proof ← mkEqTrans (mkAppN (mkConst eqName levels) xs) sourceProof
    let value ← mkLambdaFVars xs proof
    addDecl (.thmDecl {
      name := unfoldName
      levelParams := info.levelParams
      type
      value
    })
    if let some userName := privateToUserName? unfoldName then
      modifyEnv fun env => addAlias env userName unfoldName

    -- Preserve Lean's conventional equation names for the forwarding definition.
    for suffix in [eqn1ThmSuffix, unfoldThmSuffix] do
      let equationName := mkEqLikeNameFor (← getEnv) base suffix
      addDecl (.thmDecl {
        name := equationName
        levelParams := info.levelParams
        type
        value := mkConst unfoldName levels
      })
      if let some userName := privateToUserName? equationName then
        modifyEnv fun env => addAlias env userName equationName

end Veir.Buffed

/-- Declare a simulated implementation and expose its historical public name.
`inline := true` is the default; the option is forwarded unchanged as Lean's
`inline`/`noinline` compiler annotation. -/
syntax (name := buffedCmd)
  declModifiers "buffed"
    (atomic(ppSpace "(" &"inline" " := " (&"true" <|> &"false") ")"))? ppSpace
    Parser.Command.definition : command

elab_rules : command
  | `($mods:declModifiers buffed $[(inline := $flag?)]? $defn:definition) => do
    let inline := flag?.all (·.raw.getKind != `token.false)
    let mods ← Veir.Buffed.inlineModifiers mods inline
    elabCommand (← `($mods:declModifiers $defn:definition))
    let some id := defn.raw.find? (·.getKind == ``Parser.Command.declId)
      | throwError "buffed: could not find the definition's name"
    let source ← liftCoreM <| resolveGlobalConstNoOverload id[0]
    liftTermElabM <| Veir.Buffed.generateForwarder source inline
