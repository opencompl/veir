import Veir.Parser.Parser
import Veir.IR.Basic

open Veir.Parser.Lexer
open Veir.Parser

namespace Veir.Parser

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
  Parse a type, if present.
  Currently, only integer types are supported.
-/
def parseOptionalType : AttrParserM (Option MlirType) := do
  match ← peekToken with
  | { kind := .bareIdent, slice := slice } =>
    if slice.size < 2 then
      return none
    if (← (getThe ParserState)).input.getD slice.start 0 == 'i'.toUInt8 then
      let bitwidthSlice : Slice := {start := slice.start + 1, stop := slice.stop}
      let identifier := bitwidthSlice.of (← (getThe ParserState)).input
      let some _ := (String.fromUTF8? identifier).bind String.toNat? | return none
      let _ ← consumeToken
      return some ()
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
