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

/-- The dialect name as a Lean `Name` in lowercase for the `OpCode` inductive. -/
meta def mkDialectCode (d : Dialect) : Name :=
  .mkSimple <| d.getName

/-- The dialect name as a Lean `Name`. -/
meta def mkDialectCodeSimple (d : Dialect) : Name :=
  .mkSimple <| d.name

/-- The name of an operation as a `String`. -/
meta def mkOpName (d : Dialect) (op : String) : String :=
  d.getName ++ "." ++ (op.replace "__" ".") -- we replace "__" with "." to work around issues with '.' in constructor names.

end Dialect

/-- Create the following inductive: inductive OpCode where -/
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

/-- Assign each operation a distinct code, sequentially in declaration order starting at 1. -/
meta def emitEncode (ds : Array Dialect) : TermElabM Command := do
  let mut alts := #[]
  let mut code : Nat := 1
  for d in ds do
    for op in d.operations do
      alts := alts.push <| ←
        `(Lean.Parser.Term.matchAltExpr |
           | $(mkIdent d.mkDialectCode) $(mkIdent (.mkStr2 d.name op)) => $(quote code))
      code := code + 1
  `(def $(mkIdent `OpCode.encode) (op : $(mkIdent `OpCode)) : UInt32 := match op with $alts:matchAlt* )

/-- Inverse of `OpCode.encode`; unassigned codes (including 0) decode to `builtin.unregistered`. -/
meta def emitDecode (ds : Array Dialect) : TermElabM Command := do
  let mut alts := #[]
  let mut code : Nat := 1
  for d in ds do
    for op in d.operations do
      alts := alts.push <| ←
        `(Lean.Parser.Term.matchAltExpr |
           | $(quote code) => $(mkIdent d.mkDialectCode) $(mkIdent (.mkStr2 d.name op)))
      code := code + 1
  alts := alts.push <| ←
    `(Lean.Parser.Term.matchAltExpr | | _ => $(mkIdent `OpCode.builtin) $(mkIdent `Builtin.unregistered))
  `(def $(mkIdent `OpCode.decode) (code : UInt32) : $(mkIdent `OpCode) := match code with $alts:matchAlt* )

meta def emitDecodeEncode : TermElabM Command := do
  `(theorem $(mkIdent `OpCode.decode_encode) (op : $(mkIdent `OpCode)) :
      $(mkIdent `OpCode.decode) ($(mkIdent `OpCode.encode) op) = op := by
    cases op <;> (rename_i o; cases o) <;> rfl)

/-- Generates the type `OpCodes`, and its functions `fromName` and `name`. -/
elab "#generate_op_codes" : command  => do
  let ts := opCodesExt.getEntries (← getEnv)
  let env ← getEnv
  let mut dialects := #[]
  for t in ts do
    let some (.inductInfo info) := env.find? t
      | throwError m!"Type {t} is not defined or not an inductive."
    dialects := dialects.push <| mkDialect t.getString! info

  elabCommand <| ← Command.liftTermElabM <| mkOpCodeInductive dialects
  elabCommand <| ← Command.liftTermElabM <| emitFromName dialects
  elabCommand <| ← Command.liftTermElabM <| emitName dialects
  elabCommand <| ← Command.liftTermElabM <| emitEncode dialects
  elabCommand <| ← Command.liftTermElabM <| emitDecode dialects
  elabCommand <| ← Command.liftTermElabM <| emitDecodeEncode
  pure ()
