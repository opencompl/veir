import Veir.ForLean

namespace Veir.Parser

namespace Lexer

/--
  A slice in a ByteArray from the `start` index (inclusive) to the `stop` index (exclusive).
  This class should be used to avoid unnecessary copies of ByteArrays.
-/
structure Slice where
  start : Nat
  stop : Nat
deriving Inhabited, Repr

def Slice.of (slice : Slice) (array : ByteArray) : ByteArray :=
  array.extract slice.start slice.stop

/--
  Token kinds that can be produced by the lexer.
-/
inductive TokenKind
  /-- End of file token -/
  | Eof
  /--
    Identifier

    bare-id ::= (letter|[_]) (letter|digit|[_$.])*
  -/
  | BareIdent
  /--
    Identifier prefixed with an `@` symbol.

    at-ident ::= `@` (bare-id | string-literal)
  -/
  | AtIdent
  /--
    Identifier prefixed with a `#` symbol.
    `ident` only includes the identifier itself, not the `#` symbol.

    hash-ident ::= `#` bare-id
  -/
  | HashIdent
  /--
    Identifier prefixed with a `%` symbol.

    percent-ident ::= `%` bare-id
  -/
  | PercentIdent
  /--
    Identifier prefixed with a `^` symbol.

    percent-ident ::= `^` bare-id
  -/
  | CaretIdent
  /--
    Identifier suffixed with a `!` symbol.

    exclamation-ident ::= bare-id `!`
  -/
  | ExclamationIdent
  /-- Floating point literal. -/
  | FloatLit
  /-- Integer literal. -/
  | IntLit
  /-- String literal that can be encoded as UTF-8. -/
  | Utf8StringLit
  /-- String literal that cannot be encoded as UTF-8. -/
  | BytesStringLit
  /-- The `->` token. -/
  | Arrow
  /-- The `:` token. -/
  | Colon
  /-- The `,` token. -/
  | Comma
  /-- The `.`.. token. -/
  | Ellipsis
  /-- The `=` token. -/
  | Equal
  /-- The `>` token. -/
  | Greater
  /-- The `{` token. -/
  | LBrace
  /-- The `(` token. -/
  | LParen
  /-- The `[` token. -/
  | LSquare
  /-- The `<` token. -/
  | Less
  /-- The `-` token. -/
  | Minus
  /-- The `+` token. -/
  | Plus
  /-- The `?` token. -/
  | Question
  /-- The `}` token. -/
  | RBrace
  /-- The `)` token. -/
  | RParen
  /-- The `]` token. -/
  | RSquare
  /-- The `*` token. -/
  | Star
  /-- The `|` token. -/
  | VerticalBar
  /-- The `{-#` token. -/
  | FileMetadataBegin
  /-- The `#-}` token. -/
  | FileMetadataEnd
deriving Inhabited, Repr

instance TokenKind.toString : ToString TokenKind where
  toString
    | TokenKind.Eof => "Eof"
    | TokenKind.BareIdent => "BareIdent"
    | TokenKind.AtIdent => "AtIdent"
    | TokenKind.HashIdent => "HashIdent"
    | TokenKind.PercentIdent => "PercentIdent"
    | TokenKind.CaretIdent => "CaretIdent"
    | TokenKind.ExclamationIdent => "ExclamationIdent"
    | TokenKind.FloatLit => "FloatLit"
    | TokenKind.IntLit => "IntLit"
    | TokenKind.Utf8StringLit => "Utf8StringLit"
    | TokenKind.BytesStringLit => "BytesStringLit"
    | TokenKind.Arrow => "Arrow"
    | TokenKind.Colon => "Colon"
    | TokenKind.Comma => "Comma"
    | TokenKind.Ellipsis => "Ellipsis"
    | TokenKind.Equal => "Equal"
    | TokenKind.Greater => "Greater"
    | TokenKind.LBrace => "LBrace"
    | TokenKind.LParen => "LParen"
    | TokenKind.LSquare => "LSquare"
    | TokenKind.Less => "Less"
    | TokenKind.Minus => "Minus"
    | TokenKind.Plus => "Plus"
    | TokenKind.Question => "Question"
    | TokenKind.RBrace => "RBrace"
    | TokenKind.RParen => "RParen"
    | TokenKind.RSquare => "RSquare"
    | TokenKind.Star => "Star"
    | TokenKind.VerticalBar => "VerticalBar"
    | TokenKind.FileMetadataBegin => "FileMetadataBegin"
    | TokenKind.FileMetadataEnd => "FileMetadataEnd"

structure Token where
  /-- The kind of token. -/
  kind : TokenKind

  /-- The slice in the input ByteArray that corresponds to this token. -/
  slice : Slice
deriving Inhabited, Repr

deriving instance Repr for ByteArray

structure LexerState where
  /-- The input file being lexed. -/
  input : ByteArray

  /-- The current position in the input file. -/
  pos : Nat
deriving Inhabited, Repr

/-- Checks if the end of the file has been reached. -/
def LexerState.isEof (state : LexerState) : Bool :=
  state.pos >= state.input.size

/--
  Forms a token from the current lexer state, given the token start position and kind.
  The end position is taken from the current lexer state.
-/
def LexerState.formToken (state : LexerState) (kind : TokenKind) (startPos : Nat) : Token :=
  let slice := Slice.mk startPos state.pos
  Token.mk kind slice

/--
  Lex an identifier with the following grammar:
  `bare-id ::= (letter|[_]) (letter|digit|[_$.])*`

  The first character is expected to have already been consumed at position `tokStart`.
-/
partial def lexBareIdentifier (state : LexerState) (tokStart : Nat) : Token × LexerState := Id.run do
  let mut pos := state.pos
  let input := state.input
  while h: pos < input.size do
    let c := input[pos]
    if UInt8.isAlphaOrUnderscore c || UInt8.isDigit c || c == '$'.toUInt8 || c == '.'.toUInt8 then
      pos := pos + 1
    else
      break
  let newState := { state with pos := pos }
  (newState.formToken TokenKind.BareIdent tokStart, newState)

/--
  Lex the next token from the input.
-/
partial def lex (state : LexerState) : Except String (Token × LexerState) :=
  let tokStart := state.pos
  -- Check for end of file
  if h: state.isEof then
    return (state.formToken TokenKind.Eof state.pos, state)
  else
    let c := state.input[state.pos]'(by grind [LexerState.isEof])
    -- Skip whitespaces
    if c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\t'.toUInt8 || c == '\r'.toUInt8 || c == 0 then
      lex { state with pos := state.pos + 1 }
    -- Parse identifiers
    else if UInt8.isAlphaOrUnderscore c then
      let start := state.pos
      return lexBareIdentifier state tokStart
    else
      .error s!"Unexpected character '{Char.ofUInt8 c}' at position {state.pos}"

end Lexer

end Veir.Parser
