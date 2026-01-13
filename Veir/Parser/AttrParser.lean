import Veir.Parser.Parser
import Veir.IR.Basic

open Veir.Parser.Lexer
open Veir.Parser

namespace Veir.Parser

structure AttrParserState

abbrev AttrParserM := StateT AttrParserState (EStateM String ParserState)

/--
  Parse a type, if present.
  Currently, only integer types are supported.
-/
def parseOptionalType : AttrParserM (Option MlirType) := do
  match (← peekToken) with
  | {kind := .bareIdent, slice := slice : Token} =>
    if slice.size < 2 then
      return none
    if (← (getThe ParserState)).input.getD slice.start 0 == 'i'.toUInt8 then
      let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
      let identifier := bitwidthSlice.of (← (getThe ParserState)).input
      if let some _ := (String.fromUTF8? identifier).bind String.toNat? then
        let _ ← consumeToken
        return some ()
      else
        return none
    return none
  | _ => return none

/--
  Parse a type, otherwise return an error.
-/
def parseType (errorMsg : String := "type expected") : AttrParserM MlirType := do
  match ← parseOptionalType with
  | some ty => return ty
  | none => throw errorMsg

end Veir.Parser
