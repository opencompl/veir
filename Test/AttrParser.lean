import Veir.Parser.AttrParser
import Veir.IR.Basic

open Veir
open Veir.Parser

/--
  Run a parseOptionalType on the given input string.
-/
def testOptionalType (s : String) : Except String (Option MlirType) :=
  match ParserState.fromInput (s.toByteArray) with
  | .ok parser =>
    match (parseOptionalType.run' (AttrParserState.mk)).run parser with
    | .ok res _ => .ok res
    | .error err _ => .error err
  | .error err => .error err

/--
  Run a parseType on the given input string.
-/
def testType (s : String) : Except String MlirType :=
  match ParserState.fromInput (s.toByteArray) with
  | .ok parser =>
    match (parseType.run' (AttrParserState.mk)).run parser with
    | .ok res _ => .ok res
    | .error err _ => .error err
  | .error err => .error err

instance [BEq α] [BEq β] : BEq (Except α β) where
  beq
    | .ok t1, .ok t2 => t1 == t2
    | .error e1, .error e2 => e1 == e2
    | _, _ => false

/--
  Test that parsing a type in the given string succeeds and matches the expected type.
-/
def expectSuccess (s : String) (expected : MlirType) : Bool :=
  testOptionalType s == .ok (some expected) && testType s == .ok expected

/--
  Test that parsing a type in the given string returns none in the parseOptional variant,
  and returns the expected error in the parse variant.
-/
def expectMissing (s : String) : Bool :=
  testOptionalType s == .ok none && testType s == .error "type expected"

/--
  Test that parsing a type in the given string returns the expected error in both variants.
-/
def expectError (s : String) (expected : String) : Bool :=
  testOptionalType s == .error expected && testType s == .error expected

/--
  Macro to simplify test assertions. Wraps the test in #guard_msgs and #eval,
  expecting the result to be `true`.
-/
macro "#assert " e:term : command =>
  `(command| /--
    info: true
  -/
  #guard_msgs in
  #eval $e)

#assert expectError "\"" "expected '\"' in string literal"

#assert expectSuccess "i32" ()
#assert expectSuccess "i0" ()
#assert expectMissing "foo"
#assert expectMissing "i0x4"
