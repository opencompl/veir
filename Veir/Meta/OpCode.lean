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
meta def mkOpName (d : Dialect) (op : String) : String := d.getName ++ "." ++ op

end Dialect

/--
Generate an array with the names of the dialects.
-/
meta def dialectCodeArray (ds : Array Dialect) : Array Name :=
  ds.map Dialect.mkDialectCode

/--
Generate the inductive type `DialectCode` with a constructor for each dialect.
-/
meta def mkDialectCodeType (ds : Array Dialect) : TermElabM Syntax := do
  let ctors ← (dialectCodeArray ds).mapM mkCtor
  `(inductive $(mkIdent `DialectCode) where $ctors*
    deriving Inhabited, Repr, Hashable, DecidableEq)

/--
Generate a function `DialectCode.toByteArray`.
-/
meta def mkDialectCodeToByteArray (ds : Array Dialect) : TermElabM Syntax := do
  let mut alts := #[]
  for d in ds do
    alts := alts.push <| ←
      `(Lean.Parser.Term.matchAltExpr |
         | $(mkIdent (d.mkDialectCode)) => $(Syntax.mkStrLit d.getName).toByteArray)
  `(def $(mkIdent `DialectCode.toByteArray) (code : $(mkIdent `DialectCode)) :
      ByteArray := match code with $alts:matchAlt* )

/--
Generate a function `DialectCode.toName`.
-/
meta def mkDialectCodeToName (ds : Array Dialect) : TermElabM Syntax := do
  let mut alts := #[]
  for d in ds do
    alts := alts.push <| ←
      `(Lean.Parser.Term.matchAltExpr |
         | $(mkIdent (d.mkDialectCode)) => $(Syntax.mkStrLit d.getName))
  `(def $(mkIdent `DialectCode.toName) (code : $(mkIdent `DialectCode)) :
      String := match code with $alts:matchAlt* )

/--
Generate a function `DialectCode.fromName` that translates a dialect name
given as a `String` to `Option DialectCode`.
-/
meta def mkDialectCodeFromName (ds : Array Dialect) : TermElabM Syntax := do
  let mut alts := #[]
  for d in ds do
    alts := alts.push <| ←
      `(Lean.Parser.Term.matchAltExpr |
         | $(Syntax.mkStrLit d.getName) => some $(mkIdent (d.mkDialectCode)))
  alts := alts.push <| ←
    `(Lean.Parser.Term.matchAltExpr |
         | _ => none)
  `(def $(mkIdent `DialectCode.fromName) (name : String) :
      Option $(mkIdent `DialectCode) := match name with $alts:matchAlt* )

/--
Generate a function `DialectCode.fromByteArray` that translates a dialect name
given as a `ByteArray` to `Option DialectCode`.

Use a chain of `if` statements instead of a `match` because `ByteArray` does
not support pattern matching.
-/
meta def mkDialectCodeFromByteArray (ds : Array Dialect) : TermElabM Syntax := do
  let mut res : TSyntax `term ← `(Option.none)
  for d in ds do
    res ← `(if name = $(Syntax.mkStrLit d.getName).toByteArray then some $(mkIdent (d.mkDialectCode)) else $res)
  `(def $(mkIdent `DialectCode.fromByteArray) (name : ByteArray) :
      Option $(mkIdent `DialectCode) := $res)

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
  let mut res : TSyntax `term ← `(Option.none)
  for d in ds do
    for op in d.operations do
      if d.getName = "builtin" ∧ op = "unregistered" then continue
      res ← `(if name = $(Syntax.mkStrLit (d.mkOpName op)).toByteArray then some (($(mkIdent d.mkDialectCode) $(mkIdent (.mkStr2 d.name op)))) else $res)
  `(def $(mkIdent `OpCode.fromName) (name : $(mkIdent ``ByteArray)) : Option $(mkIdent `OpCode) := $res)

meta def emitName (ds : Array Dialect) : TermElabM Command := do
  let mut alts := #[]
  for d in ds do
    for op in d.operations do
      alts := alts.push <| ←
        `(Lean.Parser.Term.matchAltExpr |
           | $(mkIdent d.mkDialectCode) $(mkIdent (.mkStr2 d.name op)) => $(Syntax.mkStrLit (d.mkOpName op)).toByteArray)
  `(def $(mkIdent `OpCode.name) (op : $(mkIdent `OpCode)) : ByteArray := match op with $alts:matchAlt* )

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
-/
elab "#generate_op_codes" : command  => do
  let ts := opCodesExt.getEntries (← getEnv)
  let env ← getEnv
  let mut dialects := #[]
  for t in ts do
    let some (.inductInfo info) := env.find? t
      | throwError m!"Type {t} is not defined or not an inductive."
    dialects := dialects.push <| mkDialect t.getString! info

  elabCommand <| ← Command.liftTermElabM <| mkDialectCodeType dialects
  elabCommand <| ← Command.liftTermElabM <| mkDialectCodeToByteArray dialects
  elabCommand <| ← Command.liftTermElabM <| mkDialectCodeToName dialects
  elabCommand <| ← Command.liftTermElabM <| mkDialectCodeFromByteArray dialects
  elabCommand <| ← Command.liftTermElabM <| mkDialectCodeFromName dialects
  elabCommand <| ← Command.liftTermElabM <| mkOpCodeInductive dialects
  elabCommand <| ← Command.liftTermElabM <| emitFromName dialects
  elabCommand <| ← Command.liftTermElabM <| emitName dialects
  pure ()
