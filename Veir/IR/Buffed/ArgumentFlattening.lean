module

public import Veir.IR.Buffed.SimDefs
public import Veir.IR.Buffed.ArgumentFlatteningLemmas
public import Veir.IR.Buffed.ResultView
public import Lean
public meta import Lean.Elab.PreDefinition.PartialFixpoint.Eqns
import all Init.Internal.Order.Basic

/-!
`buffed def fooSim ... := ...` introduces a raw-argument/raw-result `fooInner`
and an inline wrapper `foo` with the original signature. Argument fields, including
erased specifications and dependent proofs, are passed unchanged. Sim result leaves
are projected to their buffered context or raw pointer; a checked projection equation
lets the wrapper restore the exact original result from an erased source reference.
No separate specification function or unchecked reconstruction is generated.
-/

open Lean Meta Elab Command

namespace Veir.Buffed

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

/-- Run a small checked proof without tactic recovery inserting `sorry`. -/
private meta def proveResult (type : Expr) (tactic : Syntax) : MetaM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar type
  let goals ← (Elab.Tactic.run goal.mvarId! (Elab.Tactic.evalTactic tactic)).run' { errToSorry := false }
  unless goals.isEmpty do throwError "buffed: result proof failed\n{goals}"
  let proof ← instantiateMVars goal
  if proof.hasSyntheticSorry then throwError "buffed: invalid result proof"
  return proof

/-- Views descend through ordinary options/products and proof subtypes. Arrays and
unrecognized result leaves retain their ordinary representations. -/
private meta partial def resultView? (type : Expr) : MetaM (Option Expr) := do
  if let some (ty, structInfo) ← splitInfo? type then
    let project ← withLocalDeclD `value ty fun value =>
      mkLambdaFVars #[value] (mkProj ty.getAppFn.constName! 0 value)
    let rawType ← forallTelescope (← inferType project) fun _ ret => pure ret
    let restore ← withLocalDeclD `reference (← mkAppM ``Erased #[ty]) fun ref =>
      withLocalDeclD `raw rawType fun raw => do
        let original ← mkAppM ``Erased.out #[ref]
        withLocalDeclD `raw_eq (← mkEq raw (mkApp project original)) fun h => do
          let ctor := (← getConstInfoInduct ty.getAppFn.constName!).ctors.head!
          let mut value := mkAppN (mkConst ctor ty.getAppFn.constLevels!) ty.getAppArgs
          value := mkApp value raw
          for i in [1:structInfo.fieldNames.size] do
            let field := mkProj ty.getAppFn.constName! i original
            let expected := (← whnf (← inferType value)).bindingDomain!
            if ← isProp expected then
              let fieldSyntax ← PrettyPrinter.delab field
              let hId := mkIdent (← h.fvarId!.getDecl).userName
              let proof ← proveResult expected (← `(tactic| (subst $hId:ident; simpa only [Erased.mk_out] using $fieldSyntax)))
              value := mkApp value proof
            else if (← inferType field).isAppOf ``Erased then
              value := mkApp value (← mkAppM ``Erased.mk #[← mkAppM ``Erased.out #[field]])
            else
              throwError "buffed: non-erased trailing result field: {field}"
          mkLambdaFVars #[ref, raw, h] value
    let law ← lambdaTelescope restore fun xs body => do
      let hId := mkIdent (← xs[2]!.fvarId!.getDecl).userName
      let goal ← mkEq body (← mkAppM ``Erased.out #[xs[0]!])
      let proof ← proveResult goal (← `(tactic| (subst $hId:ident; simp only [Erased.mk_out])))
      mkLambdaFVars xs proof
    return some (← mkAppM ``ResultView.mk #[project, restore, law])
  let type ← whnf type
  let args := type.getAppArgs
  if type.isAppOfArity ``Option 1 then
    return ← (← resultView? args[0]!).mapM fun view => mkAppM ``ResultView.option #[view]
  if type.isAppOfArity ``Prod 2 then
    let a ← resultView? args[0]!
    let b ← resultView? args[1]!
    if a.isNone && b.isNone then return none
    let a ← a.getDM (mkAppM ``ResultView.identity #[args[0]!])
    let b ← b.getDM (mkAppM ``ResultView.identity #[args[1]!])
    return some (← mkAppM ``ResultView.prod #[a, b])
  if type.isAppOfArity ``Subtype 2 then
    return ← (← resultView? args[0]!).mapM fun view => mkAppM ``ResultView.subtype #[view, args[1]!]
  return none

private meta def packResult (body : Expr) : MetaM Expr := do
  if let some view ← resultView? (← inferType body) then
    mkAppM ``ResultView.project #[view, body]
  else pure body

private meta def unpackResult (source raw property : Expr) : MetaM Expr := do
  if let some view ← resultView? (← inferType source) then
    let ref ← mkAppM ``Erased.mk #[source]
    let project ← mkAppM ``ResultView.project #[view]
    let refEq ← mkAppM ``congrArg #[project, ← mkAppM ``Erased.out_mk #[source]]
    let property ← mkEqTrans property (← mkEqSymm refEq)
    let checked ← whnf (← mkAppM ``ResultView.Checked #[view, ref])
    let value ← mkAppOptM ``Subtype.mk #[some checked.getAppArgs[0]!, some checked.getAppArgs[1]!, some raw, some property]
    mkAppM ``ResultView.unpack #[view, ref, value]
  else pure raw

syntax (name := resultTerm) "buffed_project% " "(" term ")" "(" term ")" : term
syntax (name := inferredResultTerm) "buffed_project_infer% " "(" term ")" : term

@[term_elab resultTerm]
public meta def elabResultTerm : Term.TermElab := fun stx _ => do
  let type ← Term.elabType stx[2]
  let body ← Term.elabTerm stx[5] type
  Term.synthesizeSyntheticMVarsNoPostponing
  packResult (← instantiateMVars body)

@[term_elab inferredResultTerm]
public meta def elabInferredResultTerm : Term.TermElab := fun stx _ => do
  let body ← Term.elabTerm stx[2] none
  Term.synthesizeSyntheticMVarsNoPostponing
  packResult (← instantiateMVars body)

private meta def baseName (name : Name) : CoreM Name := do
  let .str parent last := name
    | throwError "buffed: expected a definition with a `Sim` suffix"
  unless last.endsWith "Sim" && last.length > 3 do
    throwError "buffed: expected a definition with a `Sim` suffix"
  return .str parent (last.dropEnd 3).toString

/-- Thread substitutions through later binders, including types and proof arguments
that depend on an earlier context or pointer. Constructor fields are processed in
order for the same reason (in particular `IRContext.sim` depends on both fields). -/
private meta def innerDefinition (info : DefinitionVal) (flattenResult := true) : MetaM (Expr × Expr) := do
  forallTelescope info.type fun xs _ => do
    let rec go (remaining : List Expr) (old replacements locals : Array Expr) :
        MetaM (Expr × Expr) := do
      match remaining with
      | [] =>
        let body := mkAppN (mkConst info.name (info.levelParams.map Level.param)) replacements
        let body ← if flattenResult then packResult body else pure body
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
    let originalInfo ← getConstInfo original
    let flattensResult ← forallTelescope originalInfo.type fun _ ret => do pure (← resultView? ret).isSome
    let e ← Term.elabTerm source (if flattensResult then none else expectedType?)
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

private meta partial def checkResultTail (stx : Syntax) : MetaM Unit := do
  if stx.isOfKind ``recursiveCall then
    throwError "buffed: non-tail recursion with a projected result is not supported"
  stx.getArgs.forM checkResultTail

set_option maxHeartbeats 1000000 in
mutual
/-- Project result leaves, not an entire recursive result after the call. This
keeps tail calls raw instead of introducing an Option reconstruction/map cycle. -/
private meta partial def projectTail (sourceType elementType : Term) (stx : Term)
    (inDo := false) : MetaM Term := do
  if stx.raw.isOfKind ``recursiveCall then return stx
  match stx with
  | `(let $d:letDecl; $body) =>
    checkResultTail d
    let body ← projectTail sourceType elementType body inDo
    `(let $d:letDecl; $body)
  | `(have $d:letDecl; $body) =>
    checkResultTail d
    let body ← projectTail sourceType elementType body inDo
    `(have $d:letDecl; $body)
  | `(if $c then $t else $e) =>
    let t ← projectTail sourceType elementType t inDo
    let e ← projectTail sourceType elementType e inDo
    `(if $c then $t else $e)
  | `(if $h : $c then $t else $e) =>
    let t ← projectTail sourceType elementType t inDo
    let e ← projectTail sourceType elementType e inDo
    `(if $h : $c then $t else $e)
  | `(some $e) => `(some (buffed_project% ($elementType) ($e)))
  | `(none) => pure stx
  | _ =>
    if stx.raw.isOfKind ``Parser.Term.match then
      let i := stx.raw.getNumArgs - 1
      let alts := stx.raw[i]
      let alts' ← alts[0].getArgs.mapM fun alt => do
        let j := alt.getNumArgs - 1
        pure (alt.setArg j (← projectTail sourceType elementType ⟨alt[j]⟩ inDo))
      return ⟨stx.raw.setArg i (alts.setArg 0 (alts[0].setArgs alts'))⟩
    else if stx.raw.isOfKind ``Parser.Term.do then
      return ⟨stx.raw.setArg 1 (← projectDoTail sourceType elementType stx.raw[1])⟩
    else if stx.raw.getNumArgs > 0 && stx.raw[0].isToken "rlet" then
      let i := stx.raw.getNumArgs - 1
      return ⟨stx.raw.setArg i (← projectTail sourceType elementType ⟨stx.raw[i]⟩ inDo)⟩
    else
      checkResultTail stx
      if inDo then `(buffed_project_infer% ($stx))
      else `(buffed_project% ($sourceType) ($stx))

private meta partial def projectDoTail (sourceType elementType : Term) (seq : Syntax)
    (tailPos := true) : MetaM Syntax := do
  let mut items := seq[0]
  for i in [:items.getNumArgs] do
    let item := items[i]
    let stmt ← projectDoItem sourceType elementType item[0] (tailPos && i + 1 == items.getNumArgs)
    items := items.setArg i (item.setArg 0 stmt)
  return seq.setArg 0 items

private meta partial def projectDoItem (sourceType elementType : Term) (stmt : Syntax)
    (tailPos : Bool) : MetaM Syntax := do
  if stmt.isOfKind ``Parser.Term.doExpr && tailPos then
    return stmt.setArg 0 (← projectTail sourceType elementType ⟨stmt[0]⟩ true)
  else if stmt.isOfKind ``Parser.Term.doReturn && stmt[1].getNumArgs > 0 then
    let value : Term := ⟨stmt[1][0]⟩
    let value ← `(buffed_project% ($elementType) ($value))
    return stmt.setArg 1 (stmt[1].setArg 0 value)
  else if stmt.isOfKind ``Parser.Term.doIf then
    let stmt := stmt.setArg 3 (← projectDoTail sourceType elementType stmt[3] tailPos)
    let elseIfs ← stmt[4].getArgs.mapM fun branch => do
      pure (branch.setArg 3 (← projectDoTail sourceType elementType branch[3] tailPos))
    let stmt := stmt.setArg 4 (stmt[4].setArgs elseIfs)
    if stmt[5].getNumArgs > 0 then
      return stmt.setArg 5 (stmt[5].setArg 1 (← projectDoTail sourceType elementType stmt[5][1] tailPos))
    else return stmt
  else if stmt.isOfKind ``Parser.Term.doMatch then
    let i := stmt.getNumArgs - 1
    let alts := stmt[i]
    let alts' ← alts[0].getArgs.mapM fun alt => do
      let j := alt.getNumArgs - 1
      pure (alt.setArg j (← projectDoTail sourceType elementType alt[j] tailPos))
    return stmt.setArg i (alts.setArg 0 (alts[0].setArgs alts'))
  else return stmt
end

private meta def recursiveCommand (name inner : Name) (inlineInner : Bool)
    (defn : Syntax) : MetaM (TSyntax `command) := do
  let info ← getConstInfoDefn name
  let (innerType, originalCall) ← innerDefinition info false
  let levels := info.levelParams.map Level.param
  let (binders, ret, sourceType, elementType, flattenResult) ← forallTelescope innerType fun xs sourceType => do
    let sourceCall := originalCall.beta xs
    let packed ← packResult sourceCall
    let flattenResult := packed != sourceCall
    let ret ← inferType packed
    let sourceType ← whnf sourceType
    let elementType := if sourceType.isAppOfArity ``Option 1 then sourceType.getAppArgs[0]! else sourceType
    let binders ← xs.mapM fun x => do
      let d ← x.fvarId!.getDecl
      let id := mkIdent d.userName
      let ty ← syntaxOf d.type
      match d.binderInfo with
      | .default => `(Parser.Term.bracketedBinderF| ($id : $ty))
      | .implicit => `(Parser.Term.bracketedBinderF| {$id : $ty})
      | .strictImplicit => `(Parser.Term.bracketedBinderF| ⦃$id : $ty⦄)
      | .instImplicit => `(Parser.Term.bracketedBinderF| [$id : $ty])
    return (binders, ← syntaxOf ret, ← syntaxOf sourceType, ← syntaxOf elementType, flattenResult)
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
  if flattenResult then
    body ← projectTail sourceType elementType body
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
      mkLambdaFVars #[f] (← mkLambdaFVars ys (← packResult (mkAppN f args)))
  let hadm ← withLocalDeclD `bound b fun bound =>
    forallTelescope b fun args type => do
      let mut resultInst := innerArgs[1]!
      for arg in args do
        resultInst := (mkApp resultInst.headBeta.getAppArgs[2]! arg).headBeta
      let order ← mkAppOptM ``Lean.Order.CCPO.toPartialOrder #[some type, some resultInst]
      let (sourceInputs, sourceType) ← withLocalDeclD `f a fun f => do
        let value := (mkAppN (mkApp reindex f) args).headBeta
        let some call := value.find? (fun e => e.getAppFn == f)
          | throwError "buffed: missing source evaluation in result reindexing"
        return (call.getAppArgs, ← inferType call)
      let predicate ← withLocalDeclD `v sourceType fun v => do
        let projected ← packResult v
        mkLambdaFVars #[v] (← mkAppOptM ``Lean.Order.PartialOrder.rel (#[type, order, projected, mkAppN bound args].map some))
      let h ← if (← resultView? sourceType).isSome then do
        let sourceType ← whnf sourceType
        let type ← whnf type
        unless sourceType.isAppOfArity ``Option 1 && type.isAppOfArity ``Option 1 do
          throwError "buffed: unsupported projected fixed-point order: {sourceType}"
        let project ← withLocalDeclD `value sourceType fun value => do
          mkLambdaFVars #[value] (← packResult value)
        let sourceBottom ← mkAppOptM ``Option.none #[some sourceType.getAppArgs[0]!]
        let botProof ← mkEqRefl (mkApp project sourceBottom)
        mkAppM ``admissible_option_project #[project, botProof, mkAppN bound args]
      else mkAppOptM ``admissible_upper (#[type, resultInst, mkAppN bound args].map some)
      let mut h ← admissibleApplication a sourceArgs[1]! sourceInputs.toList predicate h
      for arg in args.reverse do
        h ← mkAppOptM ``Lean.Order.admissible_pi #[some a, some sourceArgs[1]!, none, none, some (← mkLambdaFVars #[arg] h)]
      mkLambdaFVars #[bound] h
  let commute ← withLocalDeclD `f a fun f => do
    let lhs := mkApp reindex (mkApp sourceArgs[2]! f)
    let rhs := mkApp innerArgs[2]! (mkApp reindex f)
    let proof ← if ← withTransparency .reducible <| isDefEq lhs rhs then mkEqRefl lhs else
      proveResult (← mkEq lhs rhs) (← `(tactic| (
        funext
        dsimp only [ResultView.project, ResultView.option, ResultView.prod, ResultView.subtype, ResultView.identity]
        try with_reducible simp only [Bind.bind, Pure.pure, Function.comp_def, Option.map_bind, Option.map_some, Option.map_none, ResultView.map_ite, ResultView.map_dite]
        all_goals (repeat' (first
          | with_reducible rfl
          | (split <;> try with_reducible simp_all only [Bind.bind, Pure.pure, Function.comp_def, Option.map_bind, Option.map_some, Option.map_none, ResultView.map_ite, ResultView.map_dite]))))))
    mkLambdaFVars #[f] proof
  let fusion ← mkAppOptM ``reindex_fix
    (#[a, b, sourceArgs[1]!, innerArgs[1]!, sourceArgs[2]!, innerArgs[2]!, sourceArgs[3]!, innerArgs[3]!, reindex].map some)
  -- Avoid eager default-transparency unification of these proof arguments: it
  -- unfolds unrelated large callees while comparing beta/eta-equivalent steps.
  -- The completed theorem application is checked by the kernel in `addDecl`.
  let equality := mkApp2 fusion hadm commute
  let view ← withLocalDeclD `g b fun g =>
    mkLambdaFVars #[g] (innerValue.replace fun e => if e == innerFix then some g else none)
  let equality ← withTransparency .reducible <| mkAppM ``congrArg #[view, equality]
  let expected ← mkEq (← packResult sourceValue) innerValue
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

/-- Functional induction can generalize a dependent pair selected by an `if`.
Split its recorded equation before simplifying dependent opcode/property arguments. -/
private meta def normalizeInductionCases : Elab.Tactic.TacticM Unit := do
  let mut result := []
  for goal in ← Elab.Tactic.getGoals do
    let equation? ← goal.withContext do
      for decl in ← getLCtx do
        if let some (_, lhs, rhs) := decl.type.eq? then
          if lhs.isAppOf ``ite || lhs.isAppOf ``dite then
            let .const constructor _ := rhs.getAppFn | continue
            if let some (.ctorInfo _) := (← getEnv).find? constructor then
              return some decl.userName
      return none
    Elab.Tactic.setGoals [goal]
    if let some name := equation? then
      let id := mkIdent name
      Elab.Tactic.evalTactic (← `(tactic| (try (split at $id:ident; all_goals (cases ($id:ident))))))
    result := result ++ (← Elab.Tactic.getGoals)
  Elab.Tactic.setGoals result

private meta def rewriteResultConditions : Elab.Tactic.TacticM Unit := do
  let mut result := []
  for goal in ← Elab.Tactic.getGoals do
    let names ← goal.withContext do
      let mut names := #[]
      for decl in ← getLCtx do
        if !decl.isLet && !decl.type.isForall && (← isProp decl.type) then
          names := names.push decl.userName
      return names
    Elab.Tactic.setGoals [goal]
    for name in names do
      let id := mkIdent name
      Elab.Tactic.evalTactic (← `(tactic| all_goals (try (first
        | with_reducible rewrite [ite_eq_left ($id:ident)]
        | with_reducible rewrite [ite_eq_right ($id:ident)]
        | with_reducible rewrite [ite_eq_right (Nat.not_lt.mpr ($id:ident))]))))
    result := result ++ (← Elab.Tactic.getGoals)
  Elab.Tactic.setGoals result

private meta def generate (name : Name) (inlineInner : Bool) (recursive := false) : MetaM Unit := do
  let info ← getConstInfoDefn name
  unless info.safety == .safe do
    throwError "buffed: expected a safe definition"
  let base ← baseName name
  let .str parent last := base | unreachable!
  let inner := .str parent (last ++ "Inner")
  let unfoldName := base ++ `unfold
  for generated in (if recursive then #[base, unfoldName, base ++ `eq_sim, base ++ `inner_eq_sim]
      else #[inner, base, unfoldName, base ++ `eq_sim, base ++ `inner_eq_sim]) do
    if (← getEnv).contains generated then
      throwError "buffed: declaration already exists: {generated}"
  unless recursive do
    let (type, value) ← innerDefinition info
    addDefinition { info with name := inner, type, value, all := [inner] } inlineInner
  let levels := info.levelParams.map Level.param
  let equality ← forallTelescope info.type fun xs _ => do
    if !recursive then
      return ← mkLambdaFVars xs (← mkEqRefl (← packResult (mkAppN (mkConst name levels) xs)))
    if (PartialFixpoint.eqnInfoExt.find? (← getEnv) name).isSome then
      return ← mkLambdaFVars xs (← partialEquality name inner xs)
    let goal ← mkForallFVars xs (← mkEq (mkAppN (mkConst inner levels) (← projectedArgs xs)) (← packResult (mkAppN (mkConst name levels) xs)))
    let proof ← mkFreshExprSyntheticOpaqueMVar goal
    let goals ← (Elab.Tactic.run proof.mvarId! do
      Elab.Tactic.evalTactic (← `(tactic| intros))
      Elab.Tactic.evalTactic (← `(tactic| fun_induction $(mkIdent name)))
      normalizeInductionCases
      Elab.Tactic.evalTactic (← `(tactic| all_goals (conv => lhs; unfold $(mkIdent inner))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals (try dsimp only [ResultView.project, ResultView.option, ResultView.prod, ResultView.subtype, ResultView.identity] at *)))
      let goals ← (← Elab.Tactic.getGoals).mapM fun g => g.withContext do
        g.replaceTargetDefEq (← normalizeSimEta (← g.getType))
      Elab.Tactic.setGoals goals
      rewriteResultConditions
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try with_reducible simp only [Bind.bind, Pure.pure, Function.comp_def, Option.map_none, Option.map_some, Option.map_bind, dite_eq_left, dite_eq_right, ite_eq_left, ite_eq_right]); (try with_reducible assumption); (try with_reducible rfl))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals (try split)))
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try contradiction); (try with_reducible assumption); (try with_reducible rfl))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try with_reducible simp_all (config := { zetaDelta := true }) only [Bind.bind, Pure.pure, Function.comp_def, Option.map_bind, Option.map_none, Option.map_some]); (try with_reducible assumption); (try with_reducible rfl))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try with_reducible simp_all (config := { zetaDelta := true })); (try with_reducible assumption); (try with_reducible rfl); (try grind))))
      Elab.Tactic.evalTactic (← `(tactic| all_goals ((try with_reducible simp only [Bind.bind, Pure.pure, Function.comp_def, Option.map_bind, Option.map_none, Option.map_some]); (try with_reducible rfl))))
      rewriteResultConditions
      Elab.Tactic.evalTactic (← `(tactic| all_goals (try with_reducible rfl)))
      ).run' { errToSorry := false }
    unless goals.isEmpty do throwError "buffed: could not prove recursive argument equivalence for {name}\n{goals}"
    let proof ← instantiateMVars proof
    return proof
  if equality.hasSyntheticSorry ||
      (equality.hasNonSyntheticSorry && !(← collectAxioms name).contains ``sorryAx) then
    throwError "buffed: invalid recursive equivalence proof for {name}"
  let rawEqName := base ++ `inner_eq_sim
  let rawEqType ← forallTelescope info.type fun xs _ => do
    mkForallFVars xs (← mkEq (mkAppN (mkConst inner levels) (← projectedArgs xs))
      (← packResult (mkAppN (mkConst name levels) xs)))
  addDecl (.thmDecl { name := rawEqName, levelParams := info.levelParams, type := rawEqType, value := equality })
  let wrapper ← forallTelescope info.type fun xs _ => do
    let source := mkAppN (mkConst name levels) xs
    let raw := mkAppN (mkConst inner levels) (← projectedArgs xs)
    let property := mkAppN (mkConst rawEqName levels) xs
    mkLambdaFVars xs (← unpackResult source raw property)
  addDefinition { info with name := base, value := wrapper, all := [base] } true
  if isProtected (← getEnv) name then
    modifyEnv fun env => addProtected (addProtected env base) inner
  let equality ← forallTelescope info.type fun xs ret => do
    if (← resultView? ret).isSome then
      let goal ← mkEq (wrapper.beta xs) (mkAppN (mkConst name levels) xs)
      let proof ← proveResult goal (← `(tactic| simp only [ResultView.unpack_eq, Erased.out_mk]))
      mkLambdaFVars xs proof
    else mkLambdaFVars xs (mkAppN (mkConst rawEqName levels) xs)
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

end Veir.Buffed

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
    let mods ← Veir.Buffed.inlineModifiers mods
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
      let base ← liftCoreM <| Veir.Buffed.baseName name
      let .str parent last := base | throwError "buffed: invalid name"
      let inner := .str parent (last ++ "Inner")
      let cmd ← liftTermElabM <| Veir.Buffed.recursiveCommand name inner inlineInner defn
      elabCommand cmd
    liftTermElabM <| Veir.Buffed.generate name inlineInner recursive
