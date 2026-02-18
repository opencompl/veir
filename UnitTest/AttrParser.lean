import Veir.Parser.AttrParser
import Veir.IR.Basic

open Veir
open Veir.Parser
open Veir.AttrParser
open Veir.Attribute

/--
  Run parseOptionalType on the given input string.
-/
def testOptionalType (s : String) : Except String (Option TypeAttr) := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseOptionalType.run' AttrParserState.mk parser

/--
  Run parseType on the given input string.
-/
def testType (s : String) : Except String TypeAttr := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseType.run' AttrParserState.mk parser

/--
  Run parseOptionalAttr on the given input string.
-/
def testOptionalAttr (s : String) : Except String (Option Attribute) := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseOptionalAttribute.run' AttrParserState.mk parser

/--
  Run parseType on the given input string.
-/
def testAttr (s : String) : Except String Attribute := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseAttribute.run' AttrParserState.mk parser

/--
  Test that parsing a type in the given string succeeds and matches the expected type.
-/
def expectSuccessType (s : String) (expected : TypeAttr) : Bool :=
  testOptionalType s = .ok (some expected) ∧ testType s = .ok expected

/--
  Test that parsing an attribute in the given string succeeds and matches the expected attribute.
-/
def expectSuccessAttr (s : String) (expected : Attribute) : Bool :=
  testOptionalAttr s = .ok (some expected) ∧ testAttr s = .ok expected

/--
  Test that parsing a type in the given string returns none in the parseOptional variant,
  and returns the expected error in the parse variant.
-/
def expectMissingType (s : String) : Bool :=
  testOptionalType s = .ok none && testType s = .error "type expected"

/--
  Test that parsing an attribute in the given string returns none in the parseOptional variant,
  and returns the expected error in the parse variant.
-/
def expectMissingAttr (s : String) : Bool :=
  testOptionalAttr s = .ok none && testAttr s = .error "attribute expected"

/--
  Test that parsing a type in the given string returns the expected error in both variants.
-/
def expectErrorType (s : String) (expected : String) : Bool :=
  testOptionalType s = .error expected && testType s = .error expected

/--
  Test that parsing an attribute in the given string returns the expected error in both variants.
-/
def expectErrorAttr (s : String) (expected : String) : Bool :=
  testOptionalAttr s = .error expected && testAttr s = .error expected

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

/-! ## General errors -/

#assert expectErrorType "\"" "expected '\"' in string literal"
#assert expectMissingType "foo"
#assert expectMissingAttr "i0x4"

/-! ## Integer types -/

#assert expectSuccessType "i32" (IntegerType.mk 32)
#assert expectSuccessType "i0" (IntegerType.mk 0)
#assert expectMissingType "i0x4"

/-! ## Types parsed as attributes -/

#assert expectSuccessAttr "i32" (IntegerType.mk 32)

/-! ## Integer attributes -/

#assert expectErrorAttr "0 : 2" "integer type expected after ':' in integer attribute"
#assert expectSuccessAttr "0 : i32" (IntegerAttr.mk 0 (IntegerType.mk 32))

/-! ## String attributes -/

#assert expectSuccessAttr "\"hello\"" (StringAttr.mk "hello".toByteArray)
#assert expectSuccessAttr "\"\"" (StringAttr.mk "".toByteArray)
#assert expectSuccessAttr "\"\\\"\"" (StringAttr.mk "\\\"".toByteArray)
#assert expectSuccessAttr "\"hello world\"" (StringAttr.mk "hello world".toByteArray)
#assert expectMissingAttr "hello"  -- bare identifier, not a string attribute

/-! ## Dialect type -/

#assert expectSuccessType "!foo<bar>" ⟨UnregisteredAttr.mk "!foo<bar>" true, by grind⟩
#assert expectSuccessType "!test.test<bar>" ⟨UnregisteredAttr.mk "!test.test<bar>" true, by grind⟩

/-! ## Dialect attribute -/

#assert expectSuccessAttr "#foo<bar>" (UnregisteredAttr.mk "#foo<bar>" false)
#assert expectSuccessAttr "#test.test<bar>" (UnregisteredAttr.mk "#test.test<bar>" false)
