import Veir.Parser.AttrParser
import Veir.IR.Basic

open Veir
open Veir.Parser
open Veir.AttrParser
open Veir.Attribute

/--
  Run parseOptionalType on the given input string.
-/
def testOptionalType (s : String) : Except String (Option TypeAttr) :=
  match ParserState.fromInput (s.toByteArray) with
  | .ok parser =>
    match parseOptionalType.run' AttrParserState.mk parser with
    | .ok res => .ok res
    | .error err => .error err
  | .error err => .error err

/--
  Run parseType on the given input string.
-/
def testType (s : String) : Except String TypeAttr :=
  match ParserState.fromInput (s.toByteArray) with
  | .ok parser =>
    match parseType.run' AttrParserState.mk parser with
    | .ok res => .ok res
    | .error err => .error err
  | .error err => .error err

/--
  Test that parsing a type in the given string succeeds and matches the expected type.
-/
def expectSuccess (s : String) (expected : TypeAttr) : Bool :=
  testOptionalType s = .ok (some expected) ∧ testType s = .ok expected

/--
  Test that parsing a type in the given string returns none in the parseOptional variant,
  and returns the expected error in the parse variant.
-/
def expectMissing (s : String) : Bool :=
  testOptionalType s = .ok none && testType s = .error "type expected"

/--
  Test that parsing a type in the given string returns the expected error in both variants.
-/
def expectError (s : String) (expected : String) : Bool :=
  testOptionalType s = .error expected && testType s = .error expected

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

#assert expectSuccess "i32" IntegerType.mk 32
#assert expectSuccess "i0" IntegerType.mk 0
#assert expectMissing "foo"
#assert expectMissing "i0x4"
