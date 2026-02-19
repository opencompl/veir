import Veir.Parser.Parser
import Veir.IR.Basic

open Veir.Parser.Lexer
open Veir.Parser

namespace Veir.AttrParser

structure AttrParserState

abbrev AttrParserM := StateT AttrParserState (EStateM String ParserState)

/--
  Execute the action with the given initial state.
  Returns the result along with the final state, or an error message.
-/
def AttrParserM.run (self : AttrParserM α)
  (attrState : AttrParserState) (parserState: ParserState) : Except String (α × AttrParserState × ParserState) :=
  match (StateT.run self attrState).run parserState with
  | .ok (a, attrState) parserState => .ok (a, attrState, parserState)
  | .error err _ => .error err

/--
  Execute the action with the given initial state.
  Returns the result or an error message.
-/
def AttrParserM.run' (self : AttrParserM α)
  (attrState : AttrParserState) (parserState: ParserState) : Except String α :=
  match self.run attrState parserState with
  | .ok (a, _, _) => .ok a
  | .error err => .error err

/--
  Parse an optional integer type.
  An integer type is represented as `i` followed by a positive integer indicating its width, e.g., `i32`.
-/
def parseOptionalIntegerType : AttrParserM (Option IntegerType) := do
  match ← peekToken with
  | { kind := .bareIdent, slice := slice } =>
    if slice.size < 2 then
      return none
    if (← (getThe ParserState)).input.getD slice.start 0 == 'i'.toUInt8 then
      let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
      let identifier := bitwidthSlice.of (← (getThe ParserState)).input
      let some bitwidth := (String.fromUTF8? identifier).bind String.toNat? | return none
      let _ ← consumeToken
      return some (IntegerType.mk bitwidth)
    return none
  | _ => return none

/--
  Parse an integer type, throwing an error if it is not present.
  An integer type is represented as `i` followed by a positive integer indicating
  its width, e.g., `i32`.
-/
def parseIntegerType (errorMsg : String := "integer type expected") : AttrParserM IntegerType := do
  match ← parseOptionalIntegerType with
  | some integerType => return integerType
  | none => throw errorMsg

/--
  Parse an integer attribute, if present.
  An integer attribute has the form `value : type`, where `value` is an integer
  literal and `type` is an integer type.
-/
def parseOptionalIntegerAttr : AttrParserM (Option IntegerAttr) := do
  let some value ← parseOptionalInteger false true
    | return none
  parsePunctuation ":"
  let integerType ← parseIntegerType "integer type expected after ':' in integer attribute"
  return some (IntegerAttr.mk value integerType)

/--
  Parse a string attribute, if present.
  Its syntax is a string literal enclosed in double quotes, e.g., `"foo"`.
-/
def parseOptionalStringAttr : AttrParserM (Option StringAttr) := do
  let some str ← parseOptionalStringLiteral
    | return none
  return some (StringAttr.mk str.toByteArray)

/--
  Parse a string attribute.
  Its syntax is a string literal enclosed in double quotes, e.g., `"foo"`.
-/
def parseStringAttr (errorMsg : String := "string attribute expected") :
    AttrParserM StringAttr := do
  match ← parseOptionalStringAttr with
  | some stringAttr => return stringAttr
  | none => throw errorMsg

/--
  Parse a unit attribute, if present.
  Its syntax is the keyword `unit`.
-/
def parseOptionalUnitAttr : AttrParserM (Option UnitAttr) := do
  if ← parseOptionalKeyword "unit".toByteArray then
    return some UnitAttr.mk
  return none

def isClosingBracket (kind : TokenKind) : Bool :=
  kind = .greater || kind = .rParen || kind = .rSquare || kind = .rBrace

def isOpeningBracket (kind : TokenKind) : Bool :=
  kind = .less || kind = .lParen || kind = .lSquare || kind = .lBrace

def matchingBracket! (kind : TokenKind) : TokenKind :=
  match kind with
  | .greater => .less
  | .rParen => .lParen
  | .rSquare => .lSquare
  | .rBrace => .lBrace
  | .less => .greater
  | .lParen => .rParen
  | .lSquare => .rSquare
  | _ => .rBrace

/--
  Parse the body of an unregistered attribute, which is a balanced
  string for `<`, `(`, `[`, `{`, and may contain string literals.
  The first `<` is expected to have already been consumed when this function is called.
  The ending `>` is not consumed by this function.
-/
private def parseUnregisteredAttrBody (startPos : Option Nat := none) : AttrParserM String := do
  let startPos := startPos.getD (← peekToken).slice.start

  /- This stack corresponds to the brackets that are still open. -/
  let mut bracketStack : Array TokenKind := #[]
  let mut endPos : Nat := 0

  /- Read tokens one by one until we close the last `>` -/
  repeat
    let token ← peekToken

    /- Open a new bracket -/
    if isOpeningBracket token.kind then
      let _ ← consumeToken
      bracketStack := bracketStack.push token.kind

    /- Close a bracket -/
    else if isClosingBracket token.kind then
      let expected := matchingBracket! token.kind
      let closingName := match token.kind with
        | .greater => "`>`" | .rParen => "`)`" | .rSquare => "`]`" | _ => "`}`"
      /- If we don't have any open bracket, either we end the parsing if
         the bracket is the last `>`, or we raise an error. -/
      if bracketStack.isEmpty then
        if token.kind == .greater then
          endPos := token.slice.start
          break
        throw s!"unexpected closing bracket {closingName} in attribute body"
      /- If we have an open bracket, check that we are closing it
         with the right bracket kind. -/
      if bracketStack.back! != expected then
        throw s!"unexpected closing bracket {closingName} in attribute body"
      let _ ← consumeToken
      bracketStack := bracketStack.pop

    /- Checking for unexpected EOF -/
    else if token.kind == .eof then
      throw "unexpected end of file before closing of attribute body"

    /- Other tokens -/
    else
      let _ ← consumeToken
  let input := (← getThe ParserState).input
  let body := (Slice.mk startPos endPos).of input
  match String.fromUTF8? body with
  | some s => return s
  | none => throw "failed converting attribute body to string"

/--
  Parse a dialect type, if present.
  A dialect attribute has the form `!dialect.name<body>`.
-/
partial def parseOptionalDialectType : AttrParserM (Option TypeAttr) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .exclamationIdent
  let some dialectName := dialectName | return none
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let value := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (⟨UnregisteredAttr.mk (String.fromUTF8! value) true, by grind⟩)

/--
  Parse a dialect attribute, if present.
  A dialect attribute has the form `#dialect.name<body>`.
-/
partial def parseOptionalDialectAttr : AttrParserM (Option Attribute) := do
  let startPos ← getPos
  let dialectName ← parseOptionalPrefixedKeyword .hashIdent
  let some dialectName := dialectName | return none
  parsePunctuation "<"
  let _ ← parseUnregisteredAttrBody
  let endPos := (← peekToken).slice.stop
  parsePunctuation ">"
  let value := (Slice.mk startPos endPos).of (← getThe ParserState).input
  return some (UnregisteredAttr.mk (String.fromUTF8! value) false)

mutual

/--
  Parse a function type, if present.
  A function type has the form `(input1, input2, ...) -> (output1, output2, ...)` or
  `(input1, input2, ...) -> output`.
-/
partial def parseOptionalFunctionType : AttrParserM (Option FunctionType) := do
  -- Parse the input types.
  let some inputs ← parseOptionalDelimitedList .paren parseType
    | return none
  -- Convert the parsed types to attributes, as FunctionType stores attributes instead
  -- of types.
  let inputs := inputs.map (fun x => x.val)
  parsePunctuation "->"
  -- Parse the output types as a list.
  match ← parseOptionalDelimitedList .paren parseType with
  | some outputs =>
    -- Convert the parsed types to attributes, as FunctionType stores attributes instead
    -- of types.
    let outputs := outputs.map (fun x => x.val)
    return some (FunctionType.mk inputs outputs)
  | none =>
    -- If there is no list of output, check for a single output type.
    let outputType ← parseType "function type output expected"
    return some (FunctionType.mk inputs #[outputType])

/--
  Parse a type, if present.
-/
partial def parseOptionalType : AttrParserM (Option TypeAttr) := do
  if let some integerType ← parseOptionalIntegerType then
    return some integerType
  if let some dialectType ← parseOptionalDialectType then
    return some dialectType
  else if let some functionType := ← parseOptionalFunctionType then
    return some functionType
  else
    return none

/--
  Parse a type, throwing an error if it is not present.
-/
partial def parseType (errorMsg : String := "type expected") : AttrParserM TypeAttr := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throw errorMsg

/--
  Parse an entry in an attribute dictionary, which has the form `name = value`
  or the shorthand `name` (equivalent to `name = unit`).
-/
partial def parseAttributeDictionaryEntry : AttrParserM (ByteArray × Attribute) := do
  let name ← parseIdentifierOrStringLiteral
  if ← parseOptionalPunctuation "=" then
    let value ← parseAttribute
    return (name, value)
  else
    return (name, UnitAttr.mk)

/--
  Parse an attribute dictionary, if present.
-/
partial def parseOptionalAttributeDictionary :
    AttrParserM (Option (Array (ByteArray × Attribute))) := do
  parseOptionalDelimitedList .braces parseAttributeDictionaryEntry

/--
  Parse an attribute dictionary, throwing an error if it is not present.
-/
partial def parseAttributeDictionary (errorMsg : String := "attribute dictionary expected") :
    AttrParserM (Array (ByteArray × Attribute)) := do
  match ← parseOptionalAttributeDictionary with
  | some dict => return dict
  | none => throw errorMsg

/--
  Parse a dictionary attribute, if present.
  A dictionary attribute has the form `{key = value, key2 = value2, ...}`.
-/
partial def parseOptionalDictionaryAttr : AttrParserM (Option DictionaryAttr) := do
  let some entries ← parseOptionalDelimitedList .braces parseAttributeDictionaryEntry
    | return none
  return some (DictionaryAttr.fromArray entries)

/--
  Parse an attribute, if present.
-/
partial def parseOptionalAttribute : AttrParserM (Option Attribute) := do
  if let some dialectAttr ← parseOptionalDialectAttr then
    return some dialectAttr
  else if let some type ← parseOptionalType then
    return some type.val
  else if let some integerAttr ← parseOptionalIntegerAttr then
    return some integerAttr
  else if let some stringAttr ← parseOptionalStringAttr then
    return some stringAttr
  else if let some unitAttr ← parseOptionalUnitAttr then
    return some unitAttr
  else if let some dictAttr ← parseOptionalDictionaryAttr then
    return some dictAttr
  else
    return none

/--
  Parse an attribute, throwing an error if it is not present.
-/
partial def parseAttribute (errorMsg : String := "attribute expected") :
    AttrParserM Attribute := do
  match ← parseOptionalAttribute with
  | some attr => return attr
  | none => throw errorMsg

end

end Veir.AttrParser
