module

public import Lean
public import Lean.EnvExtension
public meta import Veir.Meta.Attrs

open Std
open Lean Elab Command Meta

namespace Veir

meta structure Dialect where
  name : String
  operations : Array String
  deriving Inhabited, Repr

meta def mkDialect (n : String) (info : InductiveVal) : Dialect := Id.run do
  let mut ops := #[]
  for ctor in info.ctors do
    ops := ops.push ctor.getString!
  pure ⟨n, ops⟩

meta def mkCtor (n : Name) : TermElabM (TSyntax `Lean.Parser.Command.ctor) :=
  `(Lean.Parser.Command.ctor | | $(mkIdent n):ident)

meta def mkCtorWithType (n : Name × Name) : TermElabM (TSyntax `Lean.Parser.Command.ctor) :=
    `(Lean.Parser.Command.ctor | | $(mkIdent n.1):ident (op : $(mkIdent n.2)))

namespace Dialect

meta def getName (d : Dialect) : String :=
  -- TODO: should we add underscores to translate from CamelCase to snake_case?
  d.name.toLower

/--
The dialect name as a Lean `Name` in lowercase for the `OpCode` inductive.
-/
meta def mkDialectCode (d : Dialect) : Name :=
  .mkSimple <| d.getName

/--
The dialect name as a Lean `Name`.
-/
meta def mkDialectCodeSimple (d : Dialect) : Name :=
  .mkSimple <| d.name

/--
The name of an operation as a `String`. Used for `fromByteArray` and `fromName`.
-/
meta def mkOpName (d : Dialect) (op : String) : String :=
  d.getName ++ "." ++ (op.replace "__" ".") -- we replace "__" with "." to work around issues with '.' in constructor names.

end Dialect

/--
Create the following inductive:

inductive OpCode where
| arith (op : Arith)
| builtin (op : Builtin)
| func (op : Func)
| llvm (op : Llvm)
| riscv (op : Riscv)
| test (op : Test)
deriving Inhabited, Repr, Hashable, DecidableEq
-/
meta def mkOpCodeInductive (ds : Array Dialect) : TermElabM Syntax := do
  let ctors := ds.map (fun d => (d.mkDialectCode, d.mkDialectCodeSimple))
  let ctors ← ctors.mapM mkCtorWithType
  `(inductive $(mkIdent `OpCode) where $ctors*
    deriving Inhabited, Repr, Hashable, DecidableEq)

meta def emitFromName (ds : Array Dialect) : TermElabM Command := do
  let unreg : TSyntax `term := (mkIdent `Builtin.unregistered)
  let builtin : TSyntax `term := (mkIdent `OpCode.builtin)
  let mut res : TSyntax `term ← `($builtin $unreg)
  for d in ds do
    for op in d.operations do
      let op := op.replace "." "__" -- we replace "." with "__" to avoid issues with '.' in constructor names
      if d.getName = "builtin" ∧ op = "unregistered" then continue
      res ← `(if name = $(Syntax.mkStrLit (d.mkOpName op)).toByteArray then ($(mkIdent d.mkDialectCode) $(mkIdent (.mkStr2 d.name op))) else $res)
  `(def $(mkIdent `OpCode.fromName) (name : $(mkIdent ``ByteArray)) : $(mkIdent `OpCode) := $res)

meta def emitName (ds : Array Dialect) : TermElabM Command := do
  let mut alts := #[]
  for d in ds do
    for op in d.operations do
      alts := alts.push <| ←
        `(Lean.Parser.Term.matchAltExpr |
           | $(mkIdent d.mkDialectCode) $(mkIdent (.mkStr2 d.name op)) => $(Syntax.mkStrLit (d.mkOpName op)).toByteArray)
  `(def $(mkIdent `OpCode.name) (op : $(mkIdent `OpCode)) : ByteArray := match op with $alts:matchAlt* )

/--
Generate a `HasDialect OpInfo Dialect` instance for the inductive `opInfo` with
constructor `ctorName` of type `'dialectName' → 'opInfo'`.
-/
meta def mkHasDialectInstance (opInfo ctorName dialectName : Name) : TermElabM Command := do
  let hasDialect := mkIdent (Name.mkStr2 "Veir" "HasDialect")
  let dialectType := mkIdent dialectName
  let ctor := mkIdent ctorName
  let project ←
    `(fun
      | $ctor op => some op
      | _ => none)
  `(instance : $hasDialect $(mkIdent opInfo) $dialectType where
      inject := $ctor
      project := $project
      project_eq_some_iff := by
        intros opInfo op
        cases opInfo <;> simp [eq_comm]
      properties_eq := by
        intro op
        cases op <;> rfl)

/--
Generates the type `OpCodes`, and its functions `fromName` and `name`.
It does so by gathering all inductive types annotated with `@[opcodes]`.

Given an inductive type

```
@[opcodes]
inductive Arith where
| constant
| addi
| subi
```
the type `OpCodes` will contain the constructors
```
| arith_constant
| arith_addi
| arith_subi
```

Dialect types declared in imported modules are included automatically.
-/
elab "#generate_op_codes" : command => do
  let env ← getEnv
  let mut ts := #[]
  /- Gather opcodes defined in imported modules. -/
  for moduleIdx in [:env.allImportedModuleNames.size] do
    ts := ts.append <| opCodesExt.getModuleEntries env moduleIdx
  /- Gather opcodes defined in the current module. -/
  for t in opCodesExt.getEntries env do
    ts := ts.push t
  let mut dialects := #[]
  for t in ts do
    let some (.inductInfo info) := env.find? t
      | throwError m!"Type {t} is not defined or not an inductive."
    dialects := dialects.push <| mkDialect t.getString! info

  elabCommand <| ← Command.liftTermElabM <| mkOpCodeInductive dialects
  elabCommand <| ← Command.liftTermElabM <| emitFromName dialects
  elabCommand <| ← Command.liftTermElabM <| emitName dialects
  pure ()

/--
Generate a `HasDialect OpInfo Dialect` instance for every dialect constructor
of the merged `OpInfo` inductive. This command must be invoked after
`HasOpInfo OpInfo` and all dialect-local `HasDialectOpInfo` instances have been
defined.
-/
elab "#generate_has_dialect_instances" opInfo:ident : command => do
  let opInfoName ← resolveGlobalConstNoOverload opInfo
  let env ← getEnv
  let some (.inductInfo info) := env.find? opInfoName
    | throwError m!"Type {opInfoName} is not defined or not an inductive."
  for ctorName in info.ctors do
    let some (.ctorInfo ctorInfo) := env.find? ctorName
      | throwError m!"Constructor {ctorName} is not defined."
    let .forallE _ (.const dialectName _) resultType _ := ctorInfo.type
      | throwError m!"Constructor {ctorName} must have exactly one dialect opcode argument."
    unless resultType.isConstOf opInfoName do
      throwError m!"Constructor {ctorName} does not construct {opInfoName}."
    elabCommand <| ← Command.liftTermElabM <|
      mkHasDialectInstance opInfoName ctorName dialectName
