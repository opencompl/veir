module

/-
# Declarative assembly format DSL

This module implements a small declarative DSL, modelled closely on MLIR's
[`assemblyFormat`](https://mlir.llvm.org/docs/DefiningDialects/Operations/#declarative-assembly-format),
for describing the *custom* (pretty) syntax of an operation. The intent is that
a format string written for MLIR's `assemblyFormat` can be reused in VeIR with
little to no change.

The DSL is interpreted at runtime: `Format.parse` turns a format string into a
`Format` AST, and `formatPrinter` compiles that AST into a
`Veir.Printer.CustomPrinter` (printing everything after the operation's name
prefix). The generated printers are registered dialect-locally: each dialect
declares its format strings in its `Printing.lean` (e.g.
`Veir/Dialects/Func/Printing.lean`) and its `HasCustomPrinting` instance maps
them through `formatPrinter`, so they go through the exact same dispatch as
hand-written custom printers. Parsing of the custom syntax (a matching walk of
the AST in `Veir/Parser/MlirParser.lean`) is added in a follow-up; this module
only supports *printing*. The set of supported directives is the minimal subset
needed for nice function syntax (`func.return`, `func.call`); operations whose
syntax cannot be expressed declaratively (most notably `func.func`, which
mirrors MLIR's `hasCustomAssemblyFormat`) are handled by dedicated hooks
instead.

Supported elements:
* literals: `` `keyword` `` / `` `:` `` etc.
* attribute/property variables: `$name` (bound to a key in the op's property /
  attribute dictionary, exactly like an ODS-declared attribute).
* directives: `attr-dict`, `attr-dict-with-keyword`, `operands`, `results`,
  `type(...)`, `functional-type(..., ...)`, `regions`, `successors`.
* optional groups: `( ... ^ ... )?` with a single anchor element, plus an
  optional else-group `( ... )? : ( ... )`.

Notable differences from MLIR (VeIR has no per-op named operand/result schema,
so it cannot resolve a `$name` to an operand or result the way ODS does):
* `$name` always denotes an attribute/property (looked up by key `name`). SSA
  operands and results are referred to only via the `operands` / `results`
  directives, including inside `type(...)` / `functional-type(...)`.
* Because there are no operand/result *variables*, the anchor of an optional
  group may be the `operands` / `results` directive (MLIR only permits a
  variable or type directive as the anchor). This is a deliberate VeIR
  extension to compensate for the missing schema.
-/

public import Veir.Printer.Basic
public import Veir.GlobalOpInfo

namespace Veir.AssemblyFormat

public section

/-- Which positional collection a `type`/`functional-type` argument refers to. -/
inductive TypeArg where
  | operands
  | results
deriving Repr, DecidableEq, Inhabited

/-- A builtin directive in the assembly format DSL. -/
inductive Directive where
  /-- `attr-dict`: the operation's discardable attribute dictionary. -/
  | attrDict
  /-- `attr-dict-with-keyword`: same, prefixed by the `attributes` keyword. -/
  | attrDictWithKeyword
  /-- `operands`: all of the operation's operands. -/
  | operands
  /-- `results`: all of the operation's results (usable only for types). -/
  | results
  /-- `type(arg)`: the type(s) of the given collection. -/
  | typeOf (arg : TypeArg)
  /-- `functional-type(ins, outs)`: prints `(ins) -> (outs)`. -/
  | functionalType (ins : TypeArg) (outs : TypeArg)
  /-- `regions`: all of the operation's regions. -/
  | regions
  /-- `successors`: all of the operation's successor blocks. -/
  | successors
deriving Repr, Inhabited

/-- A single element of an assembly format. -/
inductive Element where
  /-- A literal keyword or punctuation, written `` `...` `` in the DSL. -/
  | literal (s : String)
  /-- A `$name` variable, bound to the property/attribute key `name`. -/
  | attrVar (name : String)
  /-- A builtin directive. -/
  | directive (d : Directive)
  /-- An optional group `( then ... )? : ( else ... )` anchored on `anchor`. -/
  | optional (thenElems : Array Element) (anchor : Nat) (elseElems : Array Element)
deriving Repr, Inhabited

/-- A parsed assembly format: a flat sequence of elements. -/
abbrev Format := Array Element

/-! ## Tokenizer -/

/-- A lexical token of the format DSL. -/
inductive Tok where
  | lit (s : String)
  | dollar (name : String)
  | word (s : String)
  | lparen | rparen | langle | rangle | comma | question | caret | colon
deriving Repr, DecidableEq, Inhabited

private def isWordChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

/-- Tokenize a format string. Whitespace outside backticks is insignificant. -/
private partial def tokenize (s : String) : Except String (Array Tok) :=
  go s.toList #[]
where
  readLit (cs : List Char) (acc : String) : String × List Char :=
    match cs with
    | [] => (acc, [])
    | c :: rest => if c == '`' then (acc, rest) else readLit rest (acc.push c)
  readWord (cs : List Char) (acc : String) : String × List Char :=
    match cs with
    | [] => (acc, [])
    | c :: rest => if isWordChar c then readWord rest (acc.push c) else (acc, c :: rest)
  go (cs : List Char) (acc : Array Tok) : Except String (Array Tok) := do
    match cs with
    | [] => return acc
    | c :: rest =>
      if c == ' ' || c == '\t' || c == '\n' || c == '\r' then go rest acc
      else if c == '`' then
        let (content, rest') := readLit rest ""
        go rest' (acc.push (.lit content))
      else if c == '$' then
        let (name, rest') := readWord rest ""
        if name.isEmpty then throw "expected identifier after '$'"
        go rest' (acc.push (.dollar name))
      else if c == '(' then go rest (acc.push .lparen)
      else if c == ')' then go rest (acc.push .rparen)
      else if c == '<' then go rest (acc.push .langle)
      else if c == '>' then go rest (acc.push .rangle)
      else if c == ',' then go rest (acc.push .comma)
      else if c == '?' then go rest (acc.push .question)
      else if c == '^' then go rest (acc.push .caret)
      else if c == ':' then go rest (acc.push .colon)
      else if isWordChar c then
        let (w, rest') := readWord (c :: rest) ""
        go rest' (acc.push (.word w))
      else throw s!"unexpected character '{c}' in assembly format"

/-! ## Parser (tokens → AST) -/

private def parseTypeArg : List Tok → Except String (TypeArg × List Tok)
  | .word "operands" :: rest => return (.operands, rest)
  | .word "results" :: rest => return (.results, rest)
  | _ => throw "expected 'operands' or 'results' as the argument of a type directive"

mutual

/-- Parse a sequence of elements until a stopping token (`)`, `?`, `: (`, or
    end of input). Detects a single `^` anchor marker. -/
private partial def parseElements (toks : List Tok) (stopAtRParen : Bool) :
    Except String (Array Element × Option Nat × List Tok) := do
  let mut acc : Array Element := #[]
  let mut anchor : Option Nat := none
  let mut toks := toks
  repeat
    match toks with
    | [] => break
    | .rparen :: _ => if stopAtRParen then break else throw "unexpected ')' in assembly format"
    | .question :: _ => break
    | .colon :: .lparen :: _ => break
    | _ =>
      let (el, toks') ← parseElement toks
      acc := acc.push el
      toks := toks'
      match toks with
      | .caret :: rest =>
        if anchor.isSome then throw "multiple anchors '^' in optional group"
        anchor := some (acc.size - 1)
        toks := rest
      | _ => pure ()
  return (acc, anchor, toks)

/-- Parse a single element. -/
private partial def parseElement : List Tok → Except String (Element × List Tok)
  | .lit s :: rest => return (.literal s, rest)
  | .dollar name :: rest => return (.attrVar name, rest)
  | .word "attr-dict" :: rest => return (.directive .attrDict, rest)
  | .word "attr-dict-with-keyword" :: rest => return (.directive .attrDictWithKeyword, rest)
  | .word "operands" :: rest => return (.directive .operands, rest)
  | .word "results" :: rest => return (.directive .results, rest)
  | .word "regions" :: rest => return (.directive .regions, rest)
  | .word "successors" :: rest => return (.directive .successors, rest)
  | .word "type" :: .lparen :: rest => do
      let (arg, rest) ← parseTypeArg rest
      match rest with
      | .rparen :: rest => return (.directive (.typeOf arg), rest)
      | _ => throw "expected ')' after type(...) argument"
  | .word "functional-type" :: .lparen :: rest => do
      let (ins, rest) ← parseTypeArg rest
      match rest with
      | .comma :: rest =>
        let (outs, rest) ← parseTypeArg rest
        match rest with
        | .rparen :: rest => return (.directive (.functionalType ins outs), rest)
        | _ => throw "expected ')' after functional-type(...) arguments"
      | _ => throw "expected ',' in functional-type(ins, outs)"
  | .word w :: _ => throw s!"unknown directive '{w}'"
  | .lparen :: rest => do
      let (thenElems, anchor, rest) ← parseElements rest true
      let (elseElems, rest) ←
        match rest with
        | .rparen :: .colon :: .lparen :: rest2 => do
            let (elseEls, _, rest3) ← parseElements rest2 true
            match rest3 with
            | .rparen :: rest4 => pure (elseEls, rest4)
            | _ => throw "expected ')' to close else-group"
        | .rparen :: rest2 => pure (#[], rest2)
        | _ => throw "expected ')' to close optional group"
      match rest with
      | .question :: rest =>
          let some a := anchor | throw "optional group requires an anchor (mark an element with '^')"
          return (.optional thenElems a elseElems, rest)
      | _ => throw "expected '?' after optional group"
  | [] => throw "unexpected end of assembly format"
  | t :: _ => throw s!"unexpected token {repr t} in assembly format"

end

/-- Parse a format string into a `Format` AST. -/
public def Format.parse (s : String) : Except String Format := do
  let toks ← tokenize s
  let (elems, anchor, rest) ← parseElements toks.toList false
  if anchor.isSome then throw "anchor '^' is only allowed inside an optional group"
  unless rest.isEmpty do throw s!"unexpected trailing tokens in assembly format"
  return elems

/-- All `$name` variables referenced anywhere in the format (including nested
    optional groups). These keys are "consumed" by the format and therefore
    elided from the `attr-dict` directive, mirroring MLIR. -/
public partial def Format.attrVarNames (fmt : Format) : List String :=
  fmt.foldl (init := []) fun acc el =>
    match el with
    | .attrVar name => acc ++ [name]
    | .optional thenElems _ elseElems =>
        acc ++ Format.attrVarNames thenElems ++ Format.attrVarNames elseElems
    | _ => acc

/-! ## Printer (AST → text)

The functions below interpret a parsed `AssemblyFormat.Format` to print an
operation in its custom (pretty) syntax. Spacing follows MLIR's convention: a
space is inserted before each element except where punctuation should hug the
surrounding tokens. Recursive printing (SSA values, regions) goes through the
`env : Printer.PrintEnv` passed to the generated printer, exactly like a
hand-written custom printer in `Veir/OpPrinters.lean`.
-/

variable {OpCode : Type} [IsOpCode OpCode]

/-- Literals that should not be preceded by a space (they hug the left token). -/
def noSpaceBefore (s : String) : Bool := s == ")" || s == "]" || s == ">" || s == "," || s == "("

/-- Literals that suppress the space after them (the next element glues on). -/
def gluesNext (s : String) : Bool := s == "(" || s == "[" || s == "<"

/-- Emit a literal with MLIR-style spacing; returns the new pending-space flag. -/
def emitLiteral (s : String) (pending : Bool) : IO Bool := do
  if pending && !noSpaceBefore s then IO.print " "
  IO.print s
  return !gluesNext s

/-- The types of all operands of `op`. -/
def operandTypes (ctx : IRContext OpCode) (op : OperationPtr) : Array TypeAttr := Id.run do
  let mut tys : Array TypeAttr := #[]
  for i in 0...(op.getNumOperands! ctx) do
    tys := tys.push ((op.getOperand! ctx i).getType! ctx)
  return tys

/-- The types of all results of `op`. -/
def resultTypes (ctx : IRContext OpCode) (op : OperationPtr) : Array TypeAttr := Id.run do
  let mut tys : Array TypeAttr := #[]
  for i in 0...(op.getNumResults! ctx) do
    tys := tys.push (((op.getResult i).get! ctx).type)
  return tys

/-- Print a comma-separated list of operands `%a, %b` (no surrounding parens). -/
def printOperandsFormat (env : Printer.PrintEnv OpCode) (ctx : IRContext OpCode) (op : OperationPtr)
    (pending : Bool) : IO Bool := do
  let n := op.getNumOperands! ctx
  if n = 0 then return pending
  if pending then IO.print " "
  env.printValue ctx (op.getOperand! ctx 0)
  for i in 1...n do
    IO.print ", "
    env.printValue ctx (op.getOperand! ctx i)
  return true

/-- Print a comma-separated list of types `t1, t2` (no surrounding parens). -/
def printCommaTypes (tys : Array TypeAttr) (pending : Bool) : IO Bool := do
  if tys.size = 0 then return pending
  if pending then IO.print " "
  IO.print s!"{tys[0]!}"
  for i in 1...tys.size do
    IO.print s!", {tys[i]!}"
  return true

/-- Print a function type `(ins) -> outs`, matching `printOperationType`'s
    result-side conventions (single result is printed without parens). -/
def printFunctionalTypeBody (ins outs : Array TypeAttr) (pending : Bool) : IO Bool := do
  if pending then IO.print " "
  IO.print "("
  if ins.size ≠ 0 then
    IO.print s!"{ins[0]!}"
    for i in 1...ins.size do
      IO.print s!", {ins[i]!}"
  IO.print ") -> "
  if outs.size = 0 then
    IO.print "()"
  else if outs.size = 1 then
    match outs[0]!.val with
    | .functionType _ => IO.print s!"({outs[0]!})"
    | _ => IO.print s!"{outs[0]!}"
  else
    IO.print "("
    IO.print s!"{outs[0]!}"
    for i in 1...outs.size do
      IO.print s!", {outs[i]!}"
    IO.print ")"
  return true

/-- Print the value of a `$name` variable, looked up first in the operation's
    properties (inherent attributes) and then in its discardable attributes.
    Absent variables print nothing. -/
def printAttrVar (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (name : String) (pending : Bool) : IO Bool := do
  let key := name.toUTF8
  let props := op.getProperties! ctx opType
  let propDict := IsOpCode.toAttrDict opType props
  let value : Option Attribute :=
    match propDict[key]? with
    | some v => some v
    | none => (((op.get! ctx).attrs).entries.find? (fun e => e.1 = key)).map (·.2)
  match value with
  | none => return pending
  | some v =>
    if pending then IO.print " "
    IO.print (toString v)
    return true

/-- Print the `attr-dict` (or `attr-dict-with-keyword`) directive: the merge of
    inherent properties and discardable attributes, excluding keys consumed by
    `$var`s elsewhere in the format. -/
def printAttrDictFormat (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (consumed : List String) (withKeyword : Bool) (pending : Bool) : IO Bool := do
  let props := op.getProperties! ctx opType
  let propDict := IsOpCode.toAttrDict opType props
  let mut entries : Array (ByteArray × Attribute) := #[]
  for (k, v) in propDict.toArray do
    if !consumed.contains (String.fromUTF8! k) then
      entries := entries.push (k, v)
  for (k, v) in ((op.get! ctx).attrs).entries do
    if !consumed.contains (String.fromUTF8! k) then
      entries := entries.push (k, v)
  if entries.size = 0 then return pending
  if pending then IO.print " "
  if withKeyword then IO.print "attributes "
  IO.print (DictionaryAttr.fromArray entries)
  return true

/-- Is the anchor element of an optional group "present" (so the group should be
    printed)? Mirrors MLIR: variadic operands/results/regions/successors are
    present when non-empty; an attribute variable is present when its key
    exists. -/
def isAnchorPresent (ctx : IRContext OpCode) (op : OperationPtr) (opType : OpCode)
    (el : Element) : Bool :=
  match el with
  | .directive .operands => op.getNumOperands! ctx > 0
  | .directive .results => op.getNumResults! ctx > 0
  | .directive .regions => op.getNumRegions! ctx > 0
  | .directive .successors => op.getNumSuccessors! ctx > 0
  | .attrVar name =>
      let key := name.toUTF8
      let props := op.getProperties! ctx opType
      let propDict := IsOpCode.toAttrDict opType props
      propDict.contains key || ((op.get! ctx).attrs).entries.any (fun e => e.1 = key)
  | _ => true

mutual
/-- Print a single assembly-format element. Returns the new pending-space flag. -/
partial def printFormatElement (env : Printer.PrintEnv OpCode) (ctx : IRContext OpCode) (op : OperationPtr)
    (opType : OpCode) (consumed : List String) (el : Element) (indent : Nat)
    (pending : Bool) : IO Bool := do
  match el with
  | .literal s => emitLiteral s pending
  | .attrVar name => printAttrVar ctx op opType name pending
  | .directive .attrDict => printAttrDictFormat ctx op opType consumed false pending
  | .directive .attrDictWithKeyword => printAttrDictFormat ctx op opType consumed true pending
  | .directive .operands => printOperandsFormat env ctx op pending
  | .directive .results => return pending
  | .directive (.typeOf .operands) => printCommaTypes (operandTypes ctx op) pending
  | .directive (.typeOf .results) => printCommaTypes (resultTypes ctx op) pending
  | .directive (.functionalType ins outs) =>
      let insTys := match ins with
        | .operands => operandTypes ctx op
        | .results => resultTypes ctx op
      let outTys := match outs with
        | .operands => operandTypes ctx op
        | .results => resultTypes ctx op
      printFunctionalTypeBody insTys outTys pending
  | .directive .regions =>
      let n := op.getNumRegions! ctx
      if n = 0 then return pending
      if pending then IO.print " "
      for i in 0...n do
        if i > 0 then IO.print " "
        env.printRegion ctx ((op.getRegion! ctx i).get! ctx) indent
      return true
  | .directive .successors =>
      let n := op.getNumSuccessors! ctx
      if n = 0 then return pending
      if pending then IO.print " "
      IO.print s!"^{(op.getSuccessor! ctx 0).id}"
      for i in 1...n do
        IO.print s!", ^{(op.getSuccessor! ctx i).id}"
      return true
  | .optional thenElems anchor elseElems =>
      let present := match thenElems[anchor]? with
        | some a => isAnchorPresent ctx op opType a
        | none => false
      if present then printFormatElements env ctx op opType consumed thenElems indent pending
      else printFormatElements env ctx op opType consumed elseElems indent pending

/-- Print a sequence of assembly-format elements. Returns the new pending-space flag. -/
partial def printFormatElements (env : Printer.PrintEnv OpCode) (ctx : IRContext OpCode) (op : OperationPtr)
    (opType : OpCode) (consumed : List String) (elems : Array Element) (indent : Nat)
    (pending : Bool) : IO Bool := do
  let mut p := pending
  for el in elems do
    p ← printFormatElement env ctx op opType consumed el indent p
  return p
end

/-- Compile a parsed assembly format into a custom printer. The returned
    printer prints everything after the operation's name prefix (printed by the
    dispatcher in `Veir/Printer.lean`), recursing through `env`. -/
def formatPrinter (fmt : Format) : Printer.CustomPrinter OpCode := fun env ctx op indent => do
  let opType := (op.get! ctx).opType
  let consumed := Format.attrVarNames fmt
  let _ ← printFormatElements env ctx op opType consumed fmt indent true
  pure ()

end -- public section

end Veir.AssemblyFormat
