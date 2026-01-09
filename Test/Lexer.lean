import Veir.Parser.Lexer

open Veir.Parser.Lexer

def lexResult (s : String) : String :=
  let res := lex (LexerState.mk (s.toByteArray) 0)
  match res with
  | .ok (tok, _) =>
    let value := String.fromUTF8! (tok.slice.of s.toByteArray)
    s!"Value: `{value}`, Kind: {tok.kind}"
  | .error err => s!"Error: {err}"

/--
  info: "Value: `foo`, Kind: BareIdent"
-/
#guard_msgs in
#eval lexResult "foo"

/--
  info: "Value: `foo`, Kind: BareIdent"
-/
#guard_msgs in
#eval lexResult " \r \x00 \n\tfoo"

/--
  info: "Value: `:`, Kind: Colon"
-/
#guard_msgs in
#eval lexResult ":"

/--
  info: "Value: `:`, Kind: Colon"
-/
#guard_msgs in
#eval lexResult ":"

/--
  info: "Value: `(`, Kind: LParen"
-/
#guard_msgs in
#eval lexResult "("

/--
  info: "Value: `)`, Kind: RParen"
-/
#guard_msgs in
#eval lexResult ")"

/--
  info: "Value: `{`, Kind: LBrace"
-/
#guard_msgs in
#eval lexResult "{"

/--
  info: "Value: `{-#`, Kind: FileMetadataBegin"
-/
#guard_msgs in
#eval lexResult "{-#"

/--
  info: "Value: `{`, Kind: LBrace"
-/
#guard_msgs in
#eval lexResult "{-"

/--
  info: "Value: `}`, Kind: RBrace"
-/
#guard_msgs in
#eval lexResult "}"

/--
  info: "Value: `[`, Kind: LSquare"
-/
#guard_msgs in
#eval lexResult "["

/--
  info: "Value: `]`, Kind: RSquare"
-/
#guard_msgs in
#eval lexResult "]"

/--
  info: "Value: `<`, Kind: Less"
-/
#guard_msgs in
#eval lexResult "<"

/--
  info: "Value: `>`, Kind: Greater"
-/
#guard_msgs in
#eval lexResult ">"

/--
  info: "Value: `=`, Kind: Equal"
-/
#guard_msgs in
#eval lexResult "="

/--
  info: "Value: `+`, Kind: Plus"
-/
#guard_msgs in
#eval lexResult "+"

/--
  info: "Value: `*`, Kind: Star"
-/
#guard_msgs in
#eval lexResult "*"

/--
  info: "Value: `?`, Kind: Question"
-/
#guard_msgs in
#eval lexResult "?"

/--
  info: "Value: `|`, Kind: VerticalBar"
-/
#guard_msgs in
#eval lexResult "|"

/--
  info: "Error: expected three consecutive '.' for an ellipsis"
-/
#guard_msgs in
#eval lexResult "."

/--
  info: "Value: `...`, Kind: Ellipsis"
-/
#guard_msgs in
#eval lexResult "..."

/--
  info: "Value: `-`, Kind: Minus"
-/
#guard_msgs in
#eval lexResult "-"

/--
  info: "Value: `->`, Kind: Arrow"
-/
#guard_msgs in
#eval lexResult "->"

/--
  info: "Value: `#-}`, Kind: FileMetadataEnd"
-/
#guard_msgs in
#eval lexResult "#-}"
