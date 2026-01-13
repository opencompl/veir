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
  Get the input being parsed.
-/
def ParserState.input (state : ParserState) : ByteArray :=
  state.lexer.input

/-
  Generic methods for parsing.
-/
section ParserStateMethods

variable [Monad m] [MonadExcept String m] [MonadStateOf ParserState m]

/--
  Consume the current token and return the updated parser state.
  Use `parseToken` or `parseOptionalToken` to consume only specific tokens.
  This function should not be used outside of the parser implementation.
-/
def consumeToken : m Token := do
  let token := (←get).currentToken
  let (nextToken, lexerState) ← ofExcept <| lex (←get).lexer
  set { lexer := lexerState, currentToken := nextToken : ParserState }
  return token

/--
  If the current token is of the expected kind, consume it and return it.
  Otherwise, return none.
-/
private def parseOptionalToken (tokType : TokenKind) : m (Option Token) := do
  if (←get).currentToken.kind = tokType then
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
  Peek at the current token without consuming it.
  This function should not be used outside of the parser implementation.
-/
def peekToken : m Token := do
  return (←get).currentToken

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

/--
  Parse optionally an identifier with grammar rule `(letter|[_]) (letter|digit|[_$.])*`.
  If the next token is an identifier, consume it and return its string slice.
  Otherwise, return none.
-/
def parseOptionalIdentifier : m (Option ByteArray) := do
  match ← parseOptionalToken .bareIdent with
  | some token => return some (token.slice.of ((← get).input))
  | none => return none

/--
  Parse an identifier with grammar rule `(letter|[_]) (letter|digit|[_$.])*`.
  Raise an error if the next token is not an identifier.
-/
def parseIdentifier (errorMsg : String := "identifier expected") : m ByteArray := do
  match ← parseOptionalIdentifier with
  | some ident => return ident
  | none => throw errorMsg

/--
  Parse optionally a specific keyword.
  The given keyword should be parseable as an identifier.
  If the next token is an identifier matching the given keyword, consume it and return it.
  Otherwise, return none.
-/
def parseOptionalKeyword (keyword : ByteArray) : m Bool := do
  match ← peekToken with
  | {kind := .bareIdent, slice := slice : Token} =>
    let ident := slice.of ((← get).input)
    if ident = keyword then
      let _ ← consumeToken
      return true
    else
      return false
  | _ => return false

/--
  Parse a specific keyword.
  The given keyword should be parseable as an identifier.
  If the next token is an identifier matching the given keyword, consume it and return it.
  Otherwise, return an error with the given message.
-/
def parseKeyword (keyword : ByteArray) (errorMsg : String := s!"expected keyword '{String.fromUTF8! keyword}'") : m Unit := do
  if ← parseOptionalKeyword keyword then
    return
  else
    throw errorMsg

/--
  Parse a boolean with grammar rule `true | false`, if present.
  If the next token is a boolean, consume it and return its value.
  Otherwise, return none.
-/
def parseOptionalBoolean : m (Option Bool) := do
  if ← parseOptionalKeyword "true".toByteArray then
    return some true
  else if ← parseOptionalKeyword "false".toByteArray then
    return some false
  else
    return none

/--
  Parse a boolean with grammar rule `true | false`.
  Raise an error if the next token is not a boolean.
-/
def parseBoolean (errorMsg : String := "boolean expected") : m Bool := do
  match ← parseOptionalBoolean with
  | some b => return b
  | none => throw errorMsg

/--
  Parse an integer literal, if present.
  The integer can either be in decimal form, hexadecimal form.
  Optionally, allow a leading `-` sign.
  Optionally, allow parsing `true` or `false` as `1` or `0`, respectively.
-/
def parseOptionalInteger (allowBoolean : Bool) (allowNegative : Bool) : m (Option Int) := do
  -- First try to parse a boolean if allowed
  if allowBoolean then
    let boolean ← parseOptionalBoolean
    if let some b := boolean then
      return some (if b then 1 else 0)

  -- Parse optional leading '-'
  let mut isNegative := false
  if allowNegative then
    isNegative := Option.isSome (← parseOptionalToken .minus)

  -- Parse the actual integer literal
  let intToken ← parseOptionalToken .intLit
  if intToken = none && isNegative then
    throw "expected integer literal after '-'"

  -- Convert the integer literal token to an Int
  if let some intToken := intToken then
    let slice := intToken.slice.of ((← get).input)
    let value :=
      if ∃ (_: slice.size > 2), slice[1] = 'x'.toUInt8 || slice[1] = 'X'.toUInt8 then
        slice.hexToNat?
      else
        (String.fromUTF8? slice).bind String.toNat?
    if let some value := value then
      if isNegative then
        return some (Int.negOfNat value)
      else
        return some (Int.ofNat value)
    else
      throw s!"internal error: failed converting '{intToken.slice.of ((← get).input)}' to an integer literal"
  else
    return none

/--
  Parse an integer literal.
  The integer can either be in decimal form, hexadecimal form.
  Optionally, allow a leading `-` sign.
  Optionally, allow parsing `true` or `false` as `1` or `0`, respectively.
-/
def parseInteger (allowBoolean : Bool) (allowNegative : Bool) (errorMsg : String := "integer expected") : m Int := do
  match ← parseOptionalInteger allowBoolean allowNegative with
  | some i => return i
  | none => throw errorMsg

end ParserStateMethods

end Veir.Parser
