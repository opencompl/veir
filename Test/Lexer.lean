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
