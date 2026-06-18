module

/-
# Declarative assembly format DSL

This module implements a small declarative DSL, modelled closely on MLIR's
[`assemblyFormat`](https://mlir.llvm.org/docs/DefiningDialects/Operations/#declarative-assembly-format),
for describing the *custom* (pretty) syntax of an operation. The intent is that
a format string written for MLIR's `assemblyFormat` can be reused in VeIR with
little to no change.

The DSL is interpreted at runtime: `Format.parse` turns a format string into a
`Format` AST, and the printer (`Veir/Printer.lean`) and parser
(`Veir/Parser/MlirParser.lean`) walk that AST. The set of supported directives
is the minimal subset needed for nice function syntax (`func.return`,
`func.call`); operations whose syntax cannot be expressed declaratively (most
notably `func.func`, which mirrors MLIR's `hasCustomAssemblyFormat`) are handled
by dedicated hooks instead.

Supported elements:
* literals: `` `keyword` `` / `` `:` `` etc.
* attribute/property variables: `$name` (bound to a key in the op's property /
  attribute dictionary, exactly like an ODS-declared attribute).
* directives: `attr-dict`, `attr-dict-with-keyword`, `operands`, `results`,
  `type(...)`, `functional-type(..., ...)`, `regions`, `successors`.
* optional groups: `( ... ^ ... )?` with a single anchor element, plus an
  optional else-group `( ... )? : ( ... )`.

Notable simplifications relative to MLIR (VeIR has no per-op named operand
groups, so operands/results are referred to positionally):
* In `type(...)` / `functional-type(...)`, the argument must be the keyword
  `operands` or `results`. A `$var` in that position is accepted and treated as
  `operands` to ease copy/paste from MLIR.
-/

public import Veir.OpCode
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
  | .dollar _ :: rest => return (.operands, rest)
  | _ => throw "expected 'operands' or 'results' as type directive argument"

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

/-! ## Registry

The set of operations that have a declarative custom syntax. This is a plain
hand-written function over `OpCode`, matching the style of `OpCode.isTerminator`
and friends in `Veir/GlobalOpInfo.lean`. Operations not listed here fall back to
the generic MLIR form (and, for `func.func`, to a dedicated hook).

These format strings are copied essentially verbatim from MLIR's `FuncOps.td`.
-/

/-- The declarative assembly format string for an operation, if it has one. -/
public def OpCode.assemblyFormatString? : OpCode → Option String
  | .func .return => some "attr-dict (operands^ `:` type(operands))?"
  | .func .call => some "$callee `(` operands `)` attr-dict `:` functional-type(operands, results)"
  | _ => none

/-- The parsed declarative assembly format for an operation, if it has one and
    parses successfully. -/
public def OpCode.assemblyFormat? (op : OpCode) : Option Format :=
  match OpCode.assemblyFormatString? op with
  | none => none
  | some s => (Format.parse s).toOption

end -- public section

/- Compile-time validation: every registered format string must parse. These
   `#guard`s fail the build if a format string is malformed, giving the DSL the
   same early-error behaviour as MLIR's tablegen-time checking. -/
#guard (Format.parse "attr-dict (operands^ `:` type(operands))?").toOption.isSome
#guard (Format.parse "$callee `(` operands `)` attr-dict `:` functional-type(operands, results)").toOption.isSome

end Veir.AssemblyFormat
