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

/--
Generate `Dialect.fromName : ByteArray → Option Dialect` from a given
inductive representing the operation opcodes of a dialect.
-/
meta def emitDialectFromName (d : Dialect) : TermElabM Command := do
  let mut res : TSyntax `term ← `(none)
  for op in d.operations do
    res ←
      `(if name = $(Syntax.mkStrLit (d.mkOpName op)).toByteArray then
          some $(mkIdent (.mkStr2 d.name op))
        else
          $res)
  `(def $(mkIdent (.mkStr2 d.name "fromName"))
      (name : $(mkIdent ``ByteArray)) : Option $(mkIdent d.mkDialectCodeSimple) := $res)

/--
Generate `Dialect.name : Dialect → ByteArray` from a given
inductive representing the operation opcodes of a dialect.
-/
meta def emitDialectName (d : Dialect) : TermElabM Command := do
  let mut alts := #[]
  for op in d.operations do
    alts := alts.push <| ←
      `(Lean.Parser.Term.matchAltExpr |
         | $(mkIdent (.mkStr2 d.name op)) => $(Syntax.mkStrLit (d.mkOpName op)).toByteArray)
  `(def $(mkIdent (.mkStr2 d.name "name"))
      (op : $(mkIdent d.mkDialectCodeSimple)) : ByteArray := match op with $alts:matchAlt* )

/-- Generate `OpCode.fromName : ByteArray → Option OpCode` from a given array of dialects. -/
meta def emitGlobalFromName (ds : Array Dialect) : TermElabM Command := do
  let mut res : TSyntax `term ← `(none)
  for d in ds do
    res ←
      `(match ($(mkIdent (.mkStr2 d.name "fromName")) name) with
        | some op => some ($(mkIdent d.mkDialectCode) op)
        | none => $res)
  `(def $(mkIdent `OpCode.fromName)
      (name : $(mkIdent ``ByteArray)) : Option $(mkIdent `OpCode) := $res)

/-- Generate `OpCode.name : OpCode → ByteArray` from a given array of dialects. -/
meta def emitGlobalName (ds : Array Dialect) : TermElabM Command := do
  let mut alts := #[]
  for d in ds do
    alts := alts.push <| ←
      `(Lean.Parser.Term.matchAltExpr |
         | $(mkIdent d.mkDialectCode) op => $(mkIdent (.mkStr2 d.name "name")) op)
  `(def $(mkIdent `OpCode.name)
      (op : $(mkIdent `OpCode)) : ByteArray := match op with $alts:matchAlt* )

/--
Generate the necessary boilerplate for a dialect inductive type.
For now, this only include generating `Dialect.fromName` and `Dialect.name`.
-/
elab "#generate_dialect" dialect:ident : command => do
  let dialectName ← resolveGlobalConstNoOverload dialect
  let env ← getEnv
  let some (.inductInfo info) := env.find? dialectName
    | throwError m!"Type {dialectName} is not defined or not an inductive."
  let d := mkDialect dialectName.getString! info
  elabCommand <| ← Command.liftTermElabM <| emitDialectFromName d
  elabCommand <| ← Command.liftTermElabM <| emitDialectName d

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
  elabCommand <| ← Command.liftTermElabM <| emitGlobalFromName dialects
  elabCommand <| ← Command.liftTermElabM <| emitGlobalName dialects
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
