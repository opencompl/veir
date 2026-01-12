import Veir.Parser.Parser

open Veir.Parser

/--
  Run a parsing function on the given input string.
-/
def testParser [ToString α] (s : String) (f : EStateM String ParserState α) : String :=
  match ParserState.fromInput (s.toByteArray) with
  | .ok parser =>
    match f.run parser with
    | .ok res _ => s!"Success: {toString res}"
    | .error err _ => s!"Error: {err}"
  | .error lexErr =>
    s!"Error: {lexErr}"

/--
  info: "Success: ()"
-/
#guard_msgs in
#eval testParser "->" (parsePunctuation "->")

/--
  info: "Success: true"
-/
#guard_msgs in
#eval testParser "..." (parseOptionalPunctuation "...")
