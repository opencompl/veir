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

def Slice.size (slice : Slice) : Nat :=
  slice.stop - slice.start

def Slice.of (slice : Slice) (array : ByteArray) : ByteArray :=
  array.extract slice.start slice.stop

/--
  Token kinds that can be produced by the lexer.
-/
inductive TokenKind
  /-- End of file token -/
  | eof
  /--
    Identifier

    bare-id ::= (letter|[_]) (letter|digit|[_$.])*
  -/
  | bareIdent
  /--
    Identifier prefixed with an `@` symbol.

    at-ident ::= `@` (bare-id | string-literal)
  -/
  | atIdent
  /--
    Identifier prefixed with a `#` symbol.
    `ident` only includes the identifier itself, not the `#` symbol.

    hash-ident ::= `#` bare-id
  -/
  | hashIdent
  /--
    Identifier prefixed with a `%` symbol.

    percent-ident ::= `%` bare-id
  -/
  | percentIdent
  /--
    Identifier prefixed with a `^` symbol.

    percent-ident ::= `^` bare-id
  -/
  | caretIdent
  /--
    Identifier suffixed with a `!` symbol.

    exclamation-ident ::= bare-id `!`
  -/
  | exclamationIdent
  /-- Floating point literal. -/
  | floatLit
  /-- Integer literal. -/
  | intLit
  /-- String literal. -/
  | stringLit
  /-- The `->` token. -/
  | arrow
  /-- The `:` token. -/
  | colon
  /-- The `,` token. -/
  | comma
  /-- The `.`.. token. -/
  | ellipsis
  /-- The `=` token. -/
  | equal
  /-- The `>` token. -/
  | greater
  /-- The `{` token. -/
  | lBrace
  /-- The `(` token. -/
  | lParen
  /-- The `[` token. -/
  | lSquare
  /-- The `<` token. -/
  | less
  /-- The `-` token. -/
  | minus
  /-- The `+` token. -/
  | plus
  /-- The `?` token. -/
  | question
  /-- The `}` token. -/
  | rBrace
  /-- The `)` token. -/
  | rParen
  /-- The `]` token. -/
  | rSquare
  /-- The `*` token. -/
  | star
  /-- The `|` token. -/
  | slash
  /-- The `/` token. -/
  | verticalBar
  /-- The `{-#` token. -/
  | fileMetadataBegin
  /-- The `#-}` token. -/
  | fileMetadataEnd
deriving Inhabited, Repr, DecidableEq

namespace TokenKind

/--
  Checks if the token kind is an at, hash, percent, caret, or exclamation identifier.
-/
@[expose, grind]
def isPrefixedIdentifier (tokenKind : TokenKind) : Bool :=
  tokenKind = .hashIdent || tokenKind = .percentIdent || tokenKind = .caretIdent ||
  tokenKind = .exclamationIdent || tokenKind = .atIdent

/--
  Returns the starting sigil character for a given prefixed identifier token kind.
-/
def startingSigil (tokenKind : TokenKind)
    (h : isPrefixedIdentifier tokenKind := by grind) : Char :=
  match tokenKind with
  | TokenKind.hashIdent => '#'
  | TokenKind.percentIdent => '%'
  | TokenKind.caretIdent => '^'
  | TokenKind.atIdent => '@'
  | _ => '!'

instance toString : ToString TokenKind where
  toString
    | TokenKind.eof => "eof"
    | TokenKind.bareIdent => "bareIdent"
    | TokenKind.atIdent => "atIdent"
    | TokenKind.hashIdent => "hashIdent"
    | TokenKind.percentIdent => "percentIdent"
    | TokenKind.caretIdent => "caretIdent"
    | TokenKind.exclamationIdent => "exclamationIdent"
    | TokenKind.floatLit => "floatLit"
    | TokenKind.intLit => "intLit"
    | TokenKind.stringLit => "stringLit"
    | TokenKind.arrow => "arrow"
    | TokenKind.colon => "colon"
    | TokenKind.comma => "comma"
    | TokenKind.ellipsis => "ellipsis"
    | TokenKind.equal => "equal"
    | TokenKind.greater => "greater"
    | TokenKind.lBrace => "lBrace"
    | TokenKind.lParen => "lParen"
    | TokenKind.lSquare => "lSquare"
    | TokenKind.less => "less"
    | TokenKind.minus => "minus"
    | TokenKind.plus => "plus"
    | TokenKind.question => "question"
    | TokenKind.rBrace => "rBrace"
    | TokenKind.rParen => "rParen"
    | TokenKind.rSquare => "rSquare"
    | TokenKind.star => "star"
    | TokenKind.slash => "slash"
    | TokenKind.verticalBar => "verticalBar"
    | TokenKind.fileMetadataBegin => "fileMetadataBegin"
    | TokenKind.fileMetadataEnd => "fileMetadataEnd"

end TokenKind

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
def LexerState.mkToken (state : LexerState) (kind : TokenKind) (startPos : Nat) : Token :=
  let slice := Slice.mk startPos state.pos
  Token.mk kind slice

/--
  Lex an identifier with the following grammar:
  `bare-id ::= (letter|[_]) (letter|digit|[_$.])*`

  The first character is expected to have already been consumed at position `tokStart`.
-/
def lexBareIdentifier (state : LexerState) (tokStart : Nat) : Token × LexerState := Id.run do
  let mut pos := state.pos
  let input := state.input
  while h: pos < input.size do
    let c := input[pos]
    if UInt8.isAlphaOrUnderscore c || UInt8.isDigit c || c == '$'.toUInt8 || c == '.'.toUInt8 then
      pos := pos + 1
    else
      break
  let newState := { state with pos := pos }
  (newState.mkToken .bareIdent tokStart, newState)

def skipComments (state : LexerState) : LexerState :=
  if h: state.isEof then
    state
  else
    let c := state.input[state.pos]'(by grind [LexerState.isEof])
    if c == '\n'.toUInt8 || c == '\r'.toUInt8 then
      {state with pos := state.pos + 1}
    else
      skipComments { state with pos := state.pos + 1 }
termination_by state.input.size - state.pos
decreasing_by
  grind [LexerState.isEof]

/--
  Lex a string literal starting with the following grammar:

  `string-literal ::= '"' [^"\n\f\v\r]* '"'`

  The opening `"` is expected to have already been consumed at position `tokStart`.
-/
def lexStringLiteral (state : LexerState) (tokStart : Nat) : Except String (Token × LexerState) := do
  if h: state.isEof then
    .error "expected '\"' in string literal"
  else
    let c := state.input[state.pos]'(by grind [LexerState.isEof])
    if c == '"'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .stringLit tokStart, newState)
    else if c == '\n'.toUInt8 then
      .error "expected '\"' in string literal"
    else if c == '\\'.toUInt8 then
      if h: state.pos + 1 < state.input.size then
        let c1 := state.input[state.pos + 1]
        if c1 == '"'.toUInt8 || c1 == '\\'.toUInt8 || c1 == 'n'.toUInt8 || c1 == 't'.toUInt8 then
          let nextState := { state with pos := state.pos + 2 }
          lexStringLiteral nextState tokStart
        else if h: state.pos + 2 < state.input.size then
          let c2 := state.input[state.pos + 2]
          if c1.isHexDigit && c2.isHexDigit then
            let nextState := { state with pos := state.pos + 3 }
            lexStringLiteral nextState tokStart
          else
            .error "unknown escape in string literal"
        else
          .error "unknown escape in string literal"
      else
        .error "unknown escape in string literal"
    else
      lexStringLiteral { state with pos := state.pos + 1 } tokStart
termination_by state.input.size - state.pos
decreasing_by
  all_goals grind [LexerState.isEof]

/--
  Lex an at-identifier with the following grammar:
  `at-id ::= `@` (bare-id | string-literal)`

  The first character `@` is expected to have already been parsed.
-/
def lexAtIdentifier (state : LexerState) (tokStart : Nat) : Except String (Token × LexerState) := do
  if h: state.isEof then
    .error "expected identifier or string literal after '@'"
  else
    let c := state.input[state.pos]'(by grind [LexerState.isEof])
    if UInt8.isAlphaOrUnderscore c then
      let (token, state) := lexBareIdentifier state tokStart
      return (LexerState.mkToken state .atIdent tokStart, state)
    else if c == '"'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      let (token, state) ← lexStringLiteral newState tokStart
      return (LexerState.mkToken state .atIdent tokStart, state)
    else
      .error "expected identifier or string literal after '@'"

/--
  Lex an identifier that starts with a prefix followed by suffix-id.
  The first character (the prefix) is expected to have already been
  consumed at position `tokStart`.

  attribute-id  ::= `#` suffix-id
  ssa-id        ::= '%' suffix-id
  block-id      ::= '^' suffix-id
  type-id       ::= '!' suffix-id
  suffix-id     ::= digit+ | (letter|id-punct) (letter|id-punct|digit)*
  id-punct      ::= `$` | `.` | `_` | `-`
-/
def lexPrefixedIdentifier (state : LexerState) (tokStart : Nat)
    (kind : TokenKind) : Except String (Token × LexerState) := do
  let errorString := match kind with
    | .hashIdent => "invalid attribute name"
    | .percentIdent => "invalid SSA name"
    | .caretIdent => "invalid block name"
    | .exclamationIdent => "invalid type name"
    | _ => "internal error: invalid kind for prefixed identifier"

  if h: state.isEof then
    .error errorString
  else
    let c := state.input[state.pos]'(by grind [LexerState.isEof])
    if UInt8.isDigit c then
      let mut pos := state.pos + 1
      let input := state.input
      while h: pos < input.size do
        let c := input[pos]
        if UInt8.isDigit c then
          pos := pos + 1
        else
          break
      let newState := { state with pos := pos }
      return (newState.mkToken kind tokStart, newState)
    else if UInt8.isAlphaOrUnderscore c || c == '$'.toUInt8 || c == '.'.toUInt8 || c == '-'.toUInt8 then
      let mut pos := state.pos + 1
      let input := state.input
      while h: pos < input.size do
        let c := input[pos]
        if UInt8.isAlphaOrUnderscore c || UInt8.isDigit c || c == '$'.toUInt8 || c == '.'.toUInt8 || c == '-'.toUInt8 then
          pos := pos + 1
        else
          break
      let newState := { state with pos := pos }
      return (newState.mkToken kind tokStart, newState)
    else
      .error errorString

/--
  Lex a number literal.

  integer-literal ::= digit+ | `0x` hex_digit+
  float-literal ::= [0-9]+[.][0-9]*([eE][-+]?[0-9]+)?
-/
def lexNumber (state : LexerState) (firstChar : UInt8) (tokStart : Nat) : Token × LexerState := Id.run do
  let mut pos := state.pos
  let input := state.input

  if h: state.isEof then
    return (state.mkToken .intLit tokStart, state)
  else
    let c1 := input[pos]'(by grind [LexerState.isEof])
    -- Hexadecimal literal
    if firstChar == '0'.toUInt8 && c1 == 'x'.toUInt8 then
      -- In MLIR, `0xi` is parsed as `0` followed by `xi`.
      if !(input.getD (pos + 1) 0).isHexDigit then
        return (state.mkToken .intLit tokStart, state)
      pos := pos + 2
      while h: pos < input.size do
        let c := input[pos]
        if c.isHexDigit then
          pos := pos + 1
        else
          break
      let newState := { state with pos := pos }
      return (newState.mkToken .intLit tokStart, newState)

    -- Handle the normal decimal case, with the starting digits
    while h: pos < input.size do
      let c := input[pos]
      if UInt8.isDigit c then
        pos := pos + 1
      else
        break

    -- Check for fractional part
    if input.getD pos 0 != '.'.toUInt8 then
      let newState := { state with pos := pos }
      return (newState.mkToken .intLit tokStart, newState)
    pos := pos + 1

    -- Parse the fractional digits
    while h: pos < input.size do
      let c := input[pos]
      if UInt8.isDigit c then
        pos := pos + 1
      else
        break

    -- Check for exponent part
    if input.getD pos 0 != 'e'.toUInt8 && input.getD pos 0 != 'E'.toUInt8 then
      let newState := { state with pos := pos }
      return (newState.mkToken .floatLit tokStart, newState)
    pos := pos + 1

    if (input.getD pos 0).isDigit ||
       ((input.getD pos 0 == '+'.toUInt8 || input.getD pos 0 == '-'.toUInt8) &&
       (input.getD (pos + 1) 0).isDigit) then
      pos := pos + 1
      while h: pos < input.size do
        let c := input[pos]
        if UInt8.isDigit c then
          pos := pos + 1
        else
          break
      let newState := { state with pos := pos }
      return (newState.mkToken .floatLit tokStart, newState)
    else
      let newState := { state with pos := pos }
      return (newState.mkToken .floatLit tokStart, newState)


/--
  Lex the next token from the input.
-/
partial def lex (state : LexerState) : Except String (Token × LexerState) :=
  let tokStart := state.pos
  -- Check for end of file
  if h: state.isEof then
    return (state.mkToken .eof state.pos, state)
  else
    let c := state.input[state.pos]'(by grind [LexerState.isEof])
    -- Skip whitespaces
    if c == ' '.toUInt8 || c == '\n'.toUInt8 || c == '\t'.toUInt8 || c == '\r'.toUInt8 || c == 0 then
      lex { state with pos := state.pos + 1 }
    -- Parse identifiers
    else if UInt8.isAlphaOrUnderscore c then
      let start := state.pos
      return lexBareIdentifier state tokStart
    -- Parse single-character tokens
    else if c == ':'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .colon tokStart, newState)
    else if c == ','.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .comma tokStart, newState)
    else if c == '('.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .lParen tokStart, newState)
    else if c == ')'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .rParen tokStart, newState)
    else if c == '}'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .rBrace tokStart, newState)
    else if c == '['.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .lSquare tokStart, newState)
    else if c == ']'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .rSquare tokStart, newState)
    else if c == '<'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .less tokStart, newState)
    else if c == '>'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .greater tokStart, newState)
    else if c == '='.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .equal tokStart, newState)
    else if c == '+'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .plus tokStart, newState)
    else if c == '*'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .star tokStart, newState)
    else if c == '?'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .question tokStart, newState)
    else if c == '|'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      return (newState.mkToken .verticalBar tokStart, newState)
    -- Parse `...`
    else if c == '.'.toUInt8 then
      if h: state.pos + 2 < state.input.size then
        let c1 := state.input[state.pos + 1]
        let c2 := state.input[state.pos + 2]
        if c1 == '.'.toUInt8 && c2 == '.'.toUInt8 then
          let newState := { state with pos := state.pos + 3 }
          return (newState.mkToken .ellipsis tokStart, newState)
        else
          .error "expected three consecutive '.' for an ellipsis"
      else
        .error "expected three consecutive '.' for an ellipsis"
    -- Parse `-` or `->`
    else if c == '-'.toUInt8 then
      if h: state.pos + 1 < state.input.size then
        let c1 := state.input[state.pos + 1]
        if c1 == '>'.toUInt8 then
          let newState := { state with pos := state.pos + 2 }
          return (newState.mkToken .arrow tokStart, newState)
        else
          let newState := { state with pos := state.pos + 1 }
          return (newState.mkToken .minus tokStart, newState)
      else
        let newState := { state with pos := state.pos + 1 }
        return (newState.mkToken .minus tokStart, newState)
    -- Parse `{` and `{-#`
    else if c == '{'.toUInt8 then
      if h: state.pos + 2 < state.input.size then
        let c1 := state.input[state.pos + 1]
        let c2 := state.input[state.pos + 2]
        if c1 == '-'.toUInt8 && c2 == '#'.toUInt8 then
          let newState := { state with pos := state.pos + 3 }
          return (newState.mkToken .fileMetadataBegin tokStart, newState)
        else
          let newState := { state with pos := state.pos + 1 }
          return (newState.mkToken .lBrace tokStart, newState)
      else
        let newState := { state with pos := state.pos + 1 }
        return (newState.mkToken .lBrace tokStart, newState)
    -- Parse `#-}`
    else if c == '#'.toUInt8 && state.pos + 2 < state.input.size
        && state.input[state.pos + 1]! == '-'.toUInt8 && state.input[state.pos + 2]! == '}'.toUInt8 then
      let newState := { state with pos := state.pos + 3 }
      return (newState.mkToken .fileMetadataEnd tokStart, newState)
    -- Parse `/` or a comment starting with `//`
    else if c == '/'.toUInt8 then
      if h: state.pos + 1 < state.input.size then
        let c1 := state.input[state.pos + 1]
        if c1 == '/'.toUInt8 then
          lex (skipComments {state with pos := state.pos + 2 })
        else
          let newState := { state with pos := state.pos + 1 }
          return (newState.mkToken .slash tokStart, newState)
      else
        let newState := { state with pos := state.pos + 1 }
        return (newState.mkToken .slash tokStart, newState)
    -- Parse string literals
    else if c == '"'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      lexStringLiteral newState tokStart
    else if c == '@'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      lexAtIdentifier newState tokStart
    else if c == '#'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      lexPrefixedIdentifier newState tokStart .hashIdent
    else if c == '%'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      lexPrefixedIdentifier newState tokStart .percentIdent
    else if c == '^'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      lexPrefixedIdentifier newState tokStart .caretIdent
    else if c == '!'.toUInt8 then
      let newState := { state with pos := state.pos + 1 }
      lexPrefixedIdentifier newState tokStart .exclamationIdent
    else if UInt8.isDigit c then
      let newState := { state with pos := state.pos + 1 }
      return lexNumber newState c tokStart
    else
      .error s!"Unexpected character '{Char.ofUInt8 c}' at position {state.pos}"

end Lexer

end Veir.Parser
