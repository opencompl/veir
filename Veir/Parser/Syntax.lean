module

public import Veir.Parser.AttrParser
public import Veir.GlobalOpInfo

public section
namespace Veir.Parser.Syntax
open Veir.Parser.Lexer Veir.AttrParser Veir.Parser.ParserError

abbrev LexM := EStateM ParserError ParserState
abbrev SyntaxM := StateT AttrParserState LexM

def getInput : SyntaxM ByteArray := do return (← getThe ParserState).input

def parseOpResult : SyntaxM (ByteArray × Nat × Location) := do
  let nameToken ← parseToken .percentIdent "operation result expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)

  /- If the next token is ':', we parse the expected result count, otherwise we return the name. -/
  if !(← parseOptionalToken .colon).isSome then
    return (name, 1, tokenPos)

  let count := (← parseInteger false false).toNat
  if count ≤ 1 then
    throwAt tokenPos "expected named operation to have at least 1 result"

  return (name, count, tokenPos)

/--
  Parse the results before an operation definition,
  either as a list of values followed by '=', or nothing.
-/
def parseOpResults : SyntaxM (Array (ByteArray × Nat × Location)) := do
  let .percentIdent := (← peekToken).kind | return #[]
  let results ← parseList parseOpResult
  parsePunctuation "=" "'=' expected after operation results"
  return results

/--
  An operand whose type has not yet been resolved.
  This is used during parsing to allow parsing operands before their types.
  Once the operation type is known, `resolveOperand` can be used to create an SSA value and
  check that the type matches with previous uses.

  `index` is used for the `%name#index` syntax to refer to an indexed result
  when multiple are defined for the same value.
-/
structure UnresolvedOperand where
  name : ByteArray
  index : Option Nat
  pos : Location

/--
  Get the name of an UnresolvedOperand as a String.
-/
def UnresolvedOperand.nameString (operand : UnresolvedOperand) : String :=
  String.fromUTF8! operand.name

/--
  Get the result index of an UnresolvedOperand. If one was not specified explicitly, this
  defaults to 0.
-/
def UnresolvedOperand.indexD (operand : UnresolvedOperand) : Nat :=
  operand.index.getD 0

instance : ToString UnresolvedOperand where
  toString operand :=
    match operand.index with
    | none => s!"%{operand.nameString}"
    | some n => s!"%{operand.nameString}#{n}"

/--
  Parse an operation operand.
  This has the syntax `%name` or `%name#resultCount`.
-/
def parseOperand : SyntaxM UnresolvedOperand := do
  let nameToken ← parseToken .percentIdent "operand expected"
  let tokenPos := nameToken.slice.start
  let name : ByteArray := { nameToken.slice with start := nameToken.slice.start + 1 }.of (← getInput)

  /- If no result number is specified, return without one. -/
  let some resultCount ← parseOptionalToken .hashIdent
    | return UnresolvedOperand.mk name none tokenPos

  /- Parse the result count as a Nat. -/
  let hashPos := resultCount.slice.start
  let resultCount := { resultCount.slice with start := resultCount.slice.start + 1 }.of (← getInput) -- skip # character
  let some resultCount := String.fromUTF8? resultCount >>= String.toNat?
    | throwAt hashPos "invalid SSA value result number"
  return UnresolvedOperand.mk name resultCount tokenPos

/--
  Parse a list of operation operands delimited by parentheses.
-/
def parseOperands : SyntaxM (Array UnresolvedOperand) := do
  parseDelimitedList .paren parseOperand

def attrParserState : SyntaxM AttrParserState := get

/--
  Parse a type, if present.
-/
def parseOptionalType : SyntaxM (Option TypeAttr) := do
  match AttrParser.parseOptionalType.run (← attrParserState) (← getThe ParserState) with
  | .ok (ty, _, parserState) =>
    set parserState
    return ty
  | .error err => throw err

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : SyntaxM TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throwAtCurrentPos errorMsg

/--
  Parse an operation type, consisting of a colon followed by a function type.
-/
def parseOperationType : SyntaxM (Array TypeAttr × Array TypeAttr) := do
  parsePunctuation ":"
  let inputs ← parseDelimitedList .paren parseType
  parsePunctuation "->"
  if (←peekToken).kind = .lParen then
    let outputs ← parseDelimitedList .paren parseType
    return (inputs, outputs)
  else
    let outputType ← parseType
    return (inputs, #[outputType])

/--
  Parse an SSA value followed by a colon and a type, if present.
  Also returns the location of the value definition.
-/
def parseTypedValue : SyntaxM (ByteArray × TypeAttr × Location) := do
  let nameToken ← parseToken .percentIdent "value expected"
  let tokenPos := nameToken.slice.start
  let slice := { nameToken.slice with start := nameToken.slice.start + 1 } -- skip % character
  let name := slice.of (← getInput)
  parsePunctuation ":"
  let ty ← parseType
  return (name, ty, tokenPos)

/--
  Parse the properties of an operation.
  The integer literals in a `mod_arith` operation's properties are kept as written (see
  `AttrParserState.rawIntegerLiterals`).
-/
def parseOpProperties (opCode : OpCode) : SyntaxM (propertiesOf opCode) := do
  let propertiesStart ← getPos
  if not (← parseOptionalPunctuation "<") then
    match Properties.fromAttrDict opCode {} with
    | .ok properties => return properties
    | .error err => throwAtCurrentPos err
  let rawIntegerLiterals :=
    (String.fromUTF8! opCode.name).startsWith "mod_arith."
  let attrState := { (← attrParserState) with rawIntegerLiterals }
  match AttrParser.parseAttributeDictionary.run attrState (← getThe ParserState) with
  | .ok (properties, _, parserState) =>
    set parserState
    parsePunctuation ">"
    match Properties.fromAttrDict opCode (Std.HashMap.ofList properties.toList) with
    | .ok properties => return properties
    | .error err => throwAt propertiesStart err
  | .error err => throw err

/--
Record the source operation name in the properties of a `builtin.unregistered`
operation.
-/
def optionallySetUnregisteredOpName (opCode : OpCode)
    (properties : propertiesOf opCode) (opName : ByteArray) :
    propertiesOf opCode :=
  match opCode, properties with
  | .builtin .unregistered, properties => UnregisteredProperties.mk opName properties.properties
  | _, properties => properties

/--
  Parse the attributes of an operation, if present.
-/
def parseOpAttributes : SyntaxM DictionaryAttr := do
  match AttrParser.parseOptionalAttributeDictionary.run (← attrParserState) (← getThe ParserState) with
  | .ok (attrs, _, parserState) =>
    set parserState
    match attrs with
    | none => return DictionaryAttr.empty
    | some attrs => return DictionaryAttr.fromArray attrs
  | .error err => throw err

def parseTypeAliasDefs : SyntaxM Unit := do
  repeat
    let startPos ← getPos
    let some name ← parseOptionalPrefixedKeyword .exclamationIdent | break
    if (← get).typeAliases.contains name then
      throwAt startPos s!"redefinition of type alias id '{String.fromUTF8! name}'"
    if name.toList.contains '.'.toUInt8 then
      throwAt startPos "type names with a '.' are reserved for dialect-defined names"
    parsePunctuation "=" "expected '=' in type alias definition"
    let type ← parseType
    modify fun state => { state with typeAliases := state.typeAliases.insert name type }


end Veir.Parser.Syntax
