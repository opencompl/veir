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
  info: "Value: `foo`, Kind: bareIdent"
-/
#guard_msgs in
#eval lexResult "foo"

/--
  info: "Value: `foo`, Kind: bareIdent"
-/
#guard_msgs in
#eval lexResult " \r \x00 \n\tfoo"

/--
  info: "Value: `:`, Kind: colon"
-/
#guard_msgs in
#eval lexResult ":"

/--
  info: "Value: `,`, Kind: comma"
-/
#guard_msgs in
#eval lexResult ","

/--
  info: "Value: `:`, Kind: colon"
-/
#guard_msgs in
#eval lexResult ":"

/--
  info: "Value: `(`, Kind: lParen"
-/
#guard_msgs in
#eval lexResult "("

/--
  info: "Value: `)`, Kind: rParen"
-/
#guard_msgs in
#eval lexResult ")"

/--
  info: "Value: `{`, Kind: lBrace"
-/
#guard_msgs in
#eval lexResult "{"

/--
  info: "Value: `{-#`, Kind: fileMetadataBegin"
-/
#guard_msgs in
#eval lexResult "{-#"

/--
  info: "Value: `{`, Kind: lBrace"
-/
#guard_msgs in
#eval lexResult "{-"

/--
  info: "Value: `}`, Kind: rBrace"
-/
#guard_msgs in
#eval lexResult "}"

/--
  info: "Value: `[`, Kind: lSquare"
-/
#guard_msgs in
#eval lexResult "["

/--
  info: "Value: `]`, Kind: rSquare"
-/
#guard_msgs in
#eval lexResult "]"

/--
  info: "Value: `<`, Kind: less"
-/
#guard_msgs in
#eval lexResult "<"

/--
  info: "Value: `>`, Kind: greater"
-/
#guard_msgs in
#eval lexResult ">"

/--
  info: "Value: `=`, Kind: equal"
-/
#guard_msgs in
#eval lexResult "="

/--
  info: "Value: `+`, Kind: plus"
-/
#guard_msgs in
#eval lexResult "+"

/--
  info: "Value: `*`, Kind: star"
-/
#guard_msgs in
#eval lexResult "*"

/--
  info: "Value: `?`, Kind: question"
-/
#guard_msgs in
#eval lexResult "?"

/--
  info: "Value: `|`, Kind: verticalBar"
-/
#guard_msgs in
#eval lexResult "|"

/--
  info: "Error: expected three consecutive '.' for an ellipsis"
-/
#guard_msgs in
#eval lexResult "."

/--
  info: "Value: `...`, Kind: ellipsis"
-/
#guard_msgs in
#eval lexResult "..."

/--
  info: "Value: `-`, Kind: minus"
-/
#guard_msgs in
#eval lexResult "-"

/--
  info: "Value: `->`, Kind: arrow"
-/
#guard_msgs in
#eval lexResult "->"

/--
  info: "Value: `#-}`, Kind: fileMetadataEnd"
-/
#guard_msgs in
#eval lexResult "#-}"

/--
  info: "Value: `/`, Kind: slash"
-/
#guard_msgs in
#eval lexResult "/"

/--
  info: "Value: `foo`, Kind: bareIdent"
-/
#guard_msgs in
#eval lexResult "// This is a comment\nfoo"

/--
  info: "Value: `foo`, Kind: bareIdent"
-/
#guard_msgs in
#eval lexResult "// This is a comment\rfoo"

/--
  info: "Value: ``, Kind: eof"
-/
#guard_msgs in
#eval lexResult "// This is a comment"

/--
  info: "Value: `\"Hello, World!\"`, Kind: stringLit"
-/
#guard_msgs in
#eval lexResult "\"Hello, World!\""

/--
  info: "Value: `\"\\n  \\\\ \\t \\\" \"`, Kind: stringLit"
-/
#guard_msgs in
#eval lexResult "\"\\n  \\\\ \\t \\\" \""

/--
  info: "Value: `\" \\00 \\d5 \\AF \"`, Kind: stringLit"
-/
#guard_msgs in
#eval lexResult "\" \\00 \\d5 \\AF \""

/--
  info: "Error: expected '\"' in string literal"
-/
#guard_msgs in
#eval lexResult "\""

/--
  info: "Error: expected '\"' in string literal"
-/
#guard_msgs in
#eval lexResult "\"\n\""

/--
  info: "Value: `@identifier`, Kind: atIdent"
-/
#guard_msgs in
#eval lexResult "@identifier"

/--
  info: "Value: `@\"identifier\"`, Kind: atIdent"
-/
#guard_msgs in
#eval lexResult "@\"identifier\""

/--
  info: "Value: `@\" \\00 \\d5 \\AF \"`, Kind: atIdent"
-/
#guard_msgs in
#eval lexResult "@\" \\00 \\d5 \\AF \""

/--
  info: "Error: expected identifier or string literal after '@'"
-/
#guard_msgs in
#eval lexResult "@2"

/--
  info: "Error: expected identifier or string literal after '@'"
-/
#guard_msgs in
#eval lexResult "@@"

/--
  info: "Error: expected identifier or string literal after '@'"
-/
#guard_msgs in
#eval lexResult "@"

/--
  info: "Value: `%00`, Kind: percentIdent"
-/
#guard_msgs in
#eval lexResult "%00"

/--
  info: "Value: `%00`, Kind: percentIdent"
-/
#guard_msgs in
#eval lexResult "%00a"

/--
  info: "Value: `%ga_bu-zo.meu$`, Kind: percentIdent"
-/
#guard_msgs in
#eval lexResult "%ga_bu-zo.meu$"

/--
  info: "Error: invalid SSA name"
-/
#guard_msgs in
#eval lexResult "% foo"

/--
  info: "Value: `#00`, Kind: hashIdent"
-/
#guard_msgs in
#eval lexResult "#00"

/--
  info: "Value: `#00`, Kind: hashIdent"
-/
#guard_msgs in
#eval lexResult "#00a"

/--
  info: "Value: `#ga_bu-zo.meu$`, Kind: hashIdent"
-/
#guard_msgs in
#eval lexResult "#ga_bu-zo.meu$"

/--
  info: "Error: invalid attribute name"
-/
#guard_msgs in
#eval lexResult "# foo"

/--
  info: "Value: `!00`, Kind: exclamationIdent"
-/
#guard_msgs in
#eval lexResult "!00"

/--
  info: "Value: `!00`, Kind: exclamationIdent"
-/
#guard_msgs in
#eval lexResult "!00a"

/--
  info: "Value: `!ga_bu-zo.meu$`, Kind: exclamationIdent"
-/
#guard_msgs in
#eval lexResult "!ga_bu-zo.meu$"

/--
  info: "Error: invalid type name"
-/
#guard_msgs in
#eval lexResult "! foo"

/--
  info: "Value: `^00`, Kind: caretIdent"
-/
#guard_msgs in
#eval lexResult "^00"

/--
  info: "Value: `^00`, Kind: caretIdent"
-/
#guard_msgs in
#eval lexResult "^00a"

/--
  info: "Value: `^ga_bu-zo.meu$`, Kind: caretIdent"
-/
#guard_msgs in
#eval lexResult "^ga_bu-zo.meu$"

/--
  info: "Error: invalid block name"
-/
#guard_msgs in
#eval lexResult "^ foo"

/--
  info: "Value: `0`, Kind: intLit"
-/
#guard_msgs in
#eval lexResult "0x"

/--
  info: "Value: `0`, Kind: intLit"
-/
#guard_msgs in
#eval lexResult "0xi"

/--
  info: "Value: `0x0123456789abcdefABCDEF`, Kind: intLit"
-/
#guard_msgs in
#eval lexResult "0x0123456789abcdefABCDEF"

/--
  info: "Value: `42`, Kind: intLit"
-/
#guard_msgs in
#eval lexResult "42"

/--
  info: "Value: `42.`, Kind: floatLit"
-/
#guard_msgs in
#eval lexResult "42."

/--
  info: "Value: `42.0`, Kind: floatLit"
-/
#guard_msgs in
#eval lexResult "42.0"

/--
  info: "Value: `3.1415926`, Kind: floatLit"
-/
#guard_msgs in
#eval lexResult "3.1415926"

/--
  info: "Value: `34.e0`, Kind: floatLit"
-/
#guard_msgs in
#eval lexResult "34.e0"

/--
  info: "Value: `34.e-23`, Kind: floatLit"
-/
#guard_msgs in
#eval lexResult "34.e-23"

/--
  info: "Value: `34.e12`, Kind: floatLit"
-/
#guard_msgs in
#eval lexResult "34.e12"
