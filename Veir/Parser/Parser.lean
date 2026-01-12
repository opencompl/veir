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

/-
  Generic methods for parsing.
-/
section ParserStateMethods

variable [Monad m] [MonadExcept String m] [MonadStateOf ParserState m]

/--
  Consume the current token and return the updated parser state.
  Use `parseToken` or `parseOptionalToken` to consume only specific tokens.
-/
private def consumeToken : m Token := do
  let token := (←get).currentToken
  let (nextToken, lexerState) ← ofExcept <| lex (←get).lexer
  set { lexer := lexerState, currentToken := nextToken : ParserState }
  return token

/--
  If the current token is of the expected kind, consume it and return it.
  Otherwise, return none.
-/
private def parseOptionalToken (tokType : TokenKind) : m (Option Token) := do
  if (←get).currentToken.kind == tokType then
    some <$> consumeToken
  else
    return none

/--
  Parse a token of the expected kind.
  If the current token is of the expected kind, consume it and return it.
  Otherwise, return an error with the given message.
-/
private def parseToken (tokType : TokenKind) (errorMsg : String) : m Token := do
  match ← parseOptionalToken tokType with
  | some token => return token
  | none => throw errorMsg

/--
  Check if the given string is a punctuation token.
  Punctuation tokens are all the textual symbols that are available to the user.
  The available punctuation symbols are `->`, `...`, `:`, `,`, `=`, `>`, `{`, `(`,
  `[`, `<`, `-`, `+`, `?`, `}`, `)`, `]`, `*`, and `|`.
-/
@[grind]
def isPunctuation (c : String) : Option TokenKind :=
  /-
  Note that the `{-#` and `#-}` symbols are not considered punctuation, as users should not
  use these symbols when implementing operation or attribute custom syntax.
  -/
  match c with
    | "->" => some .arrow
    | "..." => some .ellipsis
    | ":" => some .colon
    | "," => some .comma
    | "=" => some .equal
    | ">" => some .greater
    | "{" => some .lBrace
    | "(" => some .lParen
    | "[" => some .lSquare
    | "<" => some .less
    | "-" => some .minus
    | "+" => some .plus
    | "?" => some .question
    | "}" => some .rBrace
    | ")" => some .rParen
    | "]" => some .rSquare
    | "*" => some .star
    | "|" => some .verticalBar
    | _ => none

/--
  Parse optionally a punctuation symbol matching the given string.
  If the next token matches the given punctuation, consume it and return true.
  Otherwise, return false.
  The available punctuation symbols are `->`, `...`, `:`, `,`, `=`, `>`, `{`, `(`,
  `[`, `<`, `-`, `+`, `?`, `}`, `)`, `]`, `*`, and `|`.
-/
def parseOptionalPunctuation (c : String) (h : (isPunctuation c).isSome := by grind) : m Bool := do
  return (← parseOptionalToken ((isPunctuation c).get (by assumption))).isSome

/--
  Parse a punctuation symbol matching the given string.
  Raise an error if the next token is not the expected punctuation.
  The available punctuation symbols are `->`, `...`, `:`, `,`, `=`, `>`, `{`, `(`,
  `[`, `<`, `-`, `+`, `?`, `}`, `)`, `]`, `*`, and `|`.
-/
def parsePunctuation (c : String) (h : (isPunctuation c).isSome := by grind) : m Unit := do
  match ← parseOptionalPunctuation c with
  | true => return ()
  | false => throw s!"Expected punctuation '{c}'"

end ParserStateMethods

end Veir.Parser
