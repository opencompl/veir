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
  Parse an attribute, if present.
-/
partial def parseOptionalAttribute : AttrParserM (Option Attribute) := do
  if let some type ← parseOptionalType then
    return some type.val
  else if let some integerAttr ← parseOptionalIntegerAttr then
    return some integerAttr
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

/--
  Parse an entry in an attribute dictionary, which has the form `name = value`.
-/
partial def parseAttrDictEntry : AttrParserM (ByteArray × Attribute) := do
  let name ← parseIdentifierOrStringLiteral
  parsePunctuation "="
  let value ← parseAttribute
  return (name, value)

/--
  Parse an attribute dictionary, if present.
-/
def parseOptionalAttributeDictionary : AttrParserM (Option (Std.HashMap ByteArray Attribute)) := do
  let some array ← parseOptionalDelimitedList .braces parseAttrDictEntry
    | return none
  return some (Std.HashMap.ofArray array)

/--
  Parse an attribute dictionary, throwing an error if it is not present.
-/
def parseAttributeDictionary (errorMsg : String := "attribute dictionary expected") :
    AttrParserM (Std.HashMap ByteArray Attribute) := do
  match ← parseOptionalAttributeDictionary with
  | some dict => return dict
  | none => throw errorMsg

end Veir.AttrParser
