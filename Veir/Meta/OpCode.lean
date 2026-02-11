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

meta def Dialect.mkOpCode (d : Dialect) (op : String) : Name :=
  .mkSimple <| d.name ++ "_" ++ op

meta def Dialect.mkQualifiedOpCode (d : Dialect) (op : String) : Name :=
  .mkStr `Veir.OpCode <| d.name ++ "_" ++ op

meta def Dialect.mkOpName (d : Dialect) (op : String) : String := d.name ++ "." ++ op

meta def opCodeArray (ds : Array Dialect) : Array Name := Id.run do
  let mut ctors := #[]
  for d in ds do
    for op in d.operations do
      ctors := ctors.push (d.mkOpCode op)
  pure ctors

meta def mkOpCodeType (ds : Array Dialect) : TermElabM Syntax := do
  let ctors ← (opCodeArray ds).mapM mkCtor
  `(inductive $(mkIdent `OpCode) where $ctors*
    deriving Inhabited, Repr, Hashable, DecidableEq)

meta def emitFromName (ds : Array Dialect) : TermElabM Command := do
  let mut res : TSyntax `term := mkIdent `OpCode.builtin_unregistered
  for d in ds do
    for op in d.operations do
      if d.name = "builtin" ∧ op = "unregistered" then continue
      res ← `(if name = $(Syntax.mkStrLit (d.mkOpName op)).toByteArray then $(mkIdent (d.mkQualifiedOpCode op)) else $res)
  `(def $(mkIdent `OpCode.fromName) (name : $(mkIdent ``ByteArray)) : $(mkIdent `OpCode) := $res)

meta def emitName (ds : Array Dialect) : TermElabM Command := do
  let mut alts := #[]
  for d in ds do
    for op in d.operations do
      alts := alts.push <| ← 
        `(Lean.Parser.Term.matchAltExpr | 
           | $(mkIdent (d.mkQualifiedOpCode op)) => $(Syntax.mkStrLit (d.mkOpName op)).toByteArray)
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
    dialects := dialects.push <| mkDialect t.getString!.toLower info

  elabCommand <| ← Command.liftTermElabM <| mkOpCodeType dialects
  elabCommand <| ← Command.liftTermElabM <| emitFromName dialects
  elabCommand <| ← Command.liftTermElabM <| emitName dialects
  pure ()
