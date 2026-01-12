import Veir.Parser.Lexer
open Veir.Parser.Lexer

namespace Veir.Parser

/--
  The state of a generic parser.
  It contains the state of the lexer (which includes the input and the current
  position in the input).
  It also caches the current token produced by the lexer.
-/
structure ParserState where
  lexer : LexerState
  currentToken : Token

/--
  Create a new parser state at the beginning of the given input.
-/
def ParserState.fromInput (input : ByteArray) : Except String ParserState := do
  let lexerState := LexerState.mk input 0
  let (firstToken, lexerState) ← lex lexerState
  return ParserState.mk lexerState firstToken

/--
  Get the current position in the input.
-/
def ParserState.pos (state : ParserState) : Nat :=
  state.lexer.pos

/--
  Consume the current token and return the updated parser state.
  Use `parseToken` or `parseOptionalToken` to consume only specific tokens.
-/
def ParserState.consumeToken (state : ParserState) : Except String (Token × ParserState) := do
  let token := state.currentToken
  let (nextToken, nextLexer) ← lex state.lexer
  let nextState := { lexer := nextLexer, currentToken := nextToken }
  return (token, nextState)

/--
  If the current token is of the expected kind, consume it and return it.
  Otherwise, return none.
-/
def ParserState.parseOptionalToken (state : ParserState) (tokType : TokenKind) : Except String (Option (Token × ParserState)) := do
  if state.currentToken.kind == tokType then
    return some (← state.consumeToken)
  else
    return none

/--
  Parse a token of the expected kind.
  If the current token is of the expected kind, consume it and return it.
  Otherwise, return an error with the given message.
-/
def ParserState.parseToken (state : ParserState) (tokType : TokenKind) (errorMsg : String) : Except String (Token × ParserState) := do
  match ← state.parseOptionalToken tokType with
  | some result => return result
  | none => throw errorMsg

end Veir.Parser
