module

import all Veir.Parser.ParserError
public meta import Veir.Parser.Location

open Veir.Parser
open Veir.Parser.ParserError

/-- 1-based line:col for a byte offset into `s`. -/
def test_byteOffsetToLineCol (s : String) (o : Nat) : String :=
  let (line, col) := byteOffsetToLineCol s.toByteArray (Location.mk o)
  s!"{line}:{col}"

/-- The source line containing byte offset `o` of `s`. -/
def test_lineContaining (s : String) (o : Nat) : Option String :=
  lineContaining s.toByteArray (Location.mk o)

def diag (filename s : String) (o : Option Nat) (msg : String)
    (notes : List (Nat × String)) : IO Unit :=
  let e : ParserError := { msg, pos := o.map Location.mk, notes := notes.map fun (pos, m) => ParserErrorNote.mk m (Location.mk pos) }
  IO.print (e.format filename s.toByteArray)

/-! ## `byteOffsetToLineCol` -/

/-- info: "1:1" -/
#guard_msgs in
#eval test_byteOffsetToLineCol "abc\ndefg\nhij" 0

/-- info: "2:2" -/
#guard_msgs in
#eval test_byteOffsetToLineCol "abc\ndefg\nhij" 5

-- offset at EOF (clamped to size) lands on the last line, past its last char
/-- info: "3:4" -/
#guard_msgs in
#eval test_byteOffsetToLineCol "abc\ndefg\nhij" 20

/-! ## `lineContaining` -/

/-- info: some "abc" -/
#guard_msgs in
#eval test_lineContaining "abc\ndefg\nhij" 0

/-- info: some "defg" -/
#guard_msgs in
#eval test_lineContaining "abc\ndefg\nhij" 5

/-- info: some "hij" -/
#guard_msgs in
#eval test_lineContaining "abc\ndefg\nhij" 20

/-! ## `formatDiagnostic` -/

/-- info: test.mlir:2:2: error: error message
defg
 ^
test.mlir:1:1: note: note before
abc
^
test.mlir:3:4: note: note after
hij
   ^ -/
#guard_msgs (whitespace := exact) in
#eval! diag "test.mlir" "abc\ndefg\nhij" (some 5) "error message" [(0, "note before"), (20, "note after")]

/-! error with no source location falls back to <unknown location> -/

/-- info: <unknown location>: error: lost the position -/
#guard_msgs (whitespace := exact) in
#eval! diag "test.mlir" "abc\ndefg\nhij" none "lost the position" []

/-! non-ASCII byte in the source line suppresses the source/caret lines -/

/-- info: test.mlir:1:1: error: bad byte
    <source line not shown: it contains a non-ASCII byte> -/
#guard_msgs (whitespace := exact) in
#eval! do
  -- inject a 0xFF byte that makes the line non-UTF-8
  let src := "abc".toByteArray ++ ByteArray.mk #[0xFF] ++ "def".toByteArray
  let e : ParserError := { msg := "bad byte", pos := some (Location.mk 0) }
  IO.print (e.format "test.mlir" src)
