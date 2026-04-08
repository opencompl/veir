module

public import Lean
public import Lean.EnvExtension
public meta import Veir.Meta.Attrs

public import Veir.TC

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

meta def Dialect.getName (d : Dialect) : String :=
  d.name.toLower

meta def Dialect.mkDialectCode (d : Dialect) : Name :=
  .mkSimple <| d.getName

meta def Dialect.mkDialectCodeSimple (d : Dialect) : Name :=
  .mkSimple <| d.name

meta def Dialect.mkOpCode (d : Dialect) (op : String) : Name :=
  .mkSimple <| d.getName ++ "_" ++ op

meta def Dialect.mkQualifiedOpCode (d : Dialect) (op : String) : Name :=
  .mkStr `Veir.OpCode <| d.getName ++ "_" ++ op

meta def Dialect.mkOpName (d : Dialect) (op : String) : String := d.getName ++ "." ++ op

meta def opCodeArray (ds : Array Dialect) : Array Name := Id.run do
  let mut ctors := #[]
  for d in ds do
    for op in d.operations do
      ctors := ctors.push (d.mkOpCode op)
  pure ctors

meta def dialectCodeArray (ds : Array Dialect) : Array Name := Id.run do
  let mut ctors := #[]
  for d in ds do
    ctors := ctors.push d.mkDialectCode
  pure ctors

meta def mkOpCodeType (ds : Array Dialect) : TermElabM Syntax := do
  let ctors ← (opCodeArray ds).mapM mkCtor
  `(inductive $(mkIdent `OpCode) where $ctors*
    deriving Inhabited, Repr, Hashable, DecidableEq)

meta def mkDialectCodeType (ds : Array Dialect) : TermElabM Syntax := do
  let ctors ← (dialectCodeArray ds).mapM mkCtor
  `(inductive $(mkIdent `DialectCode) where $ctors*
    deriving Inhabited, Repr, Hashable, DecidableEq)

meta def mkDialectCodeToByteArray (ds : Array Dialect) : TermElabM Syntax := do
  let mut alts := #[]
  for d in ds do
    alts := alts.push <| ←
      `(Lean.Parser.Term.matchAltExpr |
         | $(mkIdent (d.mkDialectCode)) => $(Syntax.mkStrLit d.getName).toByteArray)
  `(def $(mkIdent `DialectCode.toByteArray) (code : $(mkIdent `DialectCode)) :
      ByteArray := match code with $alts:matchAlt* )

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
  -- Return `Option none` nothing else
  let mut res : TSyntax `term ← `(Option.none)
  for d in ds do
    res ← `(if name = $(Syntax.mkStrLit d.getName).toByteArray then some $(mkIdent (d.mkDialectCode)) else $res)
  `(def $(mkIdent `DialectCode.fromByteArray) (name : ByteArray) :
      Option $(mkIdent `DialectCode) := $res)

/--
Build an instance of this typeclass:

class DDD where
  opType : Type

Given a dialect 'Arith`, the instantiation would be:

instance : DDD where
  opType := Arith
-/
meta def mkDialectInstance (name : Name) : CommandElabM Command := do
  `(public instance : Veir.DDD where
     opType := $(mkIdent name))

/--
Create the following inductive:

inductive OpCode3 where
| arith (op : Arith)
| builtin (op : Builtin)
| func (op : Func)
| llvm (op : Llvm)
| riscv (op : Riscv)
| test (op : Test)
deriving Inhabited, Repr, Hashable, DecidableEq

-/
meta def mkOpCode3Inductive (ds : Array Dialect) : TermElabM Syntax := do
  let mut ctors := #[]
  for d in ds do
    ctors := ctors.push (d.mkDialectCode, d.mkDialectCodeSimple)

  let ctors2 ← (ctors).mapM mkCtorWithType
  `(inductive $(mkIdent `OpCode) where $ctors2*
    deriving Inhabited, Repr, Hashable, DecidableEq)

meta def mkDialectInstances (ds : Array Dialect) : CommandElabM (Array Command) := do
  ds.mapM (λ d => mkDialectInstance d.mkDialectCodeSimple)

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
  elabCommand <| ← Command.liftTermElabM <| mkOpCode3Inductive dialects
  -- elaborate the array of commands returned by `mkDialectInstances dialects`
  --let instances ← mkDialectInstances dialects
  --for inst in instances do
  --   elabCommand inst
  --elabCommand <| ← Command.liftTermElabM <| mkOpCodeType dialects
  elabCommand <| ← Command.liftTermElabM <| emitFromName dialects
  elabCommand <| ← Command.liftTermElabM <| emitName dialects
  pure ()
