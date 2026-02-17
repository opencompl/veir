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

section parsePunctuation

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

end parsePunctuation

section parseIdentifier

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "foo" (parseIdentifier)

/--
  info: "Error: custom error"
-/
#guard_msgs in
#eval testParser "->" (parseIdentifier "custom error")

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "foo" (parseOptionalIdentifier)

/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "->" (parseOptionalIdentifier)

end parseIdentifier

section parseBoolean

/--
  info: "Success: (some true)"
-/
#guard_msgs in
#eval testParser "true" (parseOptionalBoolean)

/--
  info: "Success: (some false)"
-/
#guard_msgs in
#eval testParser "false" (parseOptionalBoolean)

/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "0" (parseOptionalBoolean)

/--
  info: "Success: true"
-/
#guard_msgs in
#eval testParser "true" (parseBoolean)

/--
  info: "Error: error message"
-/
#guard_msgs in
#eval testParser "no" (parseBoolean "error message")

end parseBoolean

section parseInteger

-- Test with basic decimal integer
/--
  info: "Success: (some 123)"
-/
#guard_msgs in
#eval testParser "123" (parseOptionalInteger false false)

-- Test with hexadecimal integers
/--
  info: "Success: (some 1375488932539311409843695)"
-/
#guard_msgs in
#eval testParser "0x0123456789abcdefABCDEF" (parseOptionalInteger false false)

-- Test with negative integers and hex when allowed
/--
  info: "Success: (some -240)"
-/
#guard_msgs in
#eval testParser "-0xf0" (parseOptionalInteger false true)

-- Test parseOptionalInteger with negative integers and hex when disallowed
/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "-0xff" (parseOptionalInteger false false)

-- Test with negative integer when allowed
/--
  info: "Success: (some -42)"
-/
#guard_msgs in
#eval testParser "-42" (parseOptionalInteger false true)

-- Test with negative integer when not allowed
/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "-42" (parseOptionalInteger false false)

-- Test with boolean literals (when allowed)
/--
  info: "Success: (some 1)"
-/
#guard_msgs in
#eval testParser "true" (parseOptionalInteger true false)

/--
  info: "Success: (some 0)"
-/
#guard_msgs in
#eval testParser "false" (parseOptionalInteger true false)

-- Test with boolean literals (when not allowed)
/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "true" (parseOptionalInteger false false)

-- Test with non-integer input
/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "foo" (parseOptionalInteger false false)

-- Test parseInteger
/--
  info: "Success: 123"
-/
#guard_msgs in
#eval testParser "123" (parseInteger false false)

end parseInteger

section parseKeyword

/--
  info: "Success: ()"
-/
#guard_msgs in
#eval testParser "while" (parseKeyword "while".toByteArray)

/--
  info: "Error: expected keyword 'if'"
-/
#guard_msgs in
#eval testParser "while" (parseKeyword "if".toByteArray)

/--
  info: "Success: true"
-/
#guard_msgs in
#eval testParser "for" (parseOptionalKeyword "for".toByteArray)

/--
  info: "Success: false"
-/#guard_msgs in
#eval testParser "while" (parseOptionalKeyword "for".toByteArray)

end parseKeyword

section parseStringLiteral

/--
  info: "Success: hello world!"
-/
#guard_msgs in
#eval testParser "\"hello world!\"" parseStringLiteral

/--
  info: "Error: string literal expected"
-/
#guard_msgs in
#eval testParser "hello world!" parseStringLiteral

/--
  info: "Error: expected '\"' in string literal"
-/
#guard_msgs in
#eval testParser "\"unterminated string" parseStringLiteral

/--
  info: "Success: \\n"
-/
#guard_msgs in
#eval testParser "\"\\n\"" parseStringLiteral

/--
  info: "Success: (some (hello world!))"
-/
#guard_msgs in
#eval testParser "\"hello world!\"" parseOptionalStringLiteral

end parseStringLiteral

section parseList

/-! # Test different delimiters. -/

/--
  info: "Success: #[1, 2, 3]"
-/
#guard_msgs in
#eval testParser "(1, 2, 3)" (parseDelimitedList .paren (parseInteger false false))

/--
  info: "Success: #[1, 2, 3]"
-/
#guard_msgs in
#eval testParser "[1, 2, 3]" (parseDelimitedList .square (parseInteger false false))

/--
  info: "Success: #[1, 2, 3]"
-/
#guard_msgs in
#eval testParser "{1, 2, 3}" (parseDelimitedList .braces (parseInteger false false))

/--
  info: "Success: #[1, 2, 3]"
-/
#guard_msgs in
#eval testParser "<1, 2, 3>" (parseDelimitedList .angle (parseInteger false false))

/-! # Test some error cases. -/

/--
  info: "Error: closing delimiter ')' expected"
-/
#guard_msgs in
#eval testParser "(1, 2, 3" (parseDelimitedList .paren (parseInteger false false))

/--
  info: "Error: integer expected"
-/
#guard_msgs in
#eval testParser "(1, 2, " (parseDelimitedList .paren (parseInteger false false))

/--
  info: "Error: integer expected"
-/
#guard_msgs in
#eval testParser "(1, 2, )" (parseDelimitedList .paren (parseInteger false false))

/-! # Test empty list. -/

/--
  info: "Success: #[]"
-/
#guard_msgs in
#eval testParser "()" (parseDelimitedList .paren (parseInteger false false))

/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "" (parseOptionalDelimitedList .paren (parseInteger false false))

/-! # Test no delimiter and optional delimiter cases. -/

/--
  info: "Success: #[3, 2]"
-/
#guard_msgs in
#eval testParser "3, 2" (parseList (parseInteger false false))

/--
  info: "Success: (some #[3, 2])"
-/
#guard_msgs in
#eval testParser "(3, 2)" (parseOptionalDelimitedList .paren (parseInteger false false))

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "foo" parseOptionalIdentifierOrStringLiteral

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "foo" parseIdentifierOrStringLiteral

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "\"foo\"" parseOptionalIdentifierOrStringLiteral

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "\"foo\"" parseIdentifierOrStringLiteral

/-! # Test `parsePrefixedKeyword` -/

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "@foo" (parsePrefixedKeyword .atIdent)

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "@foo" (parseOptionalPrefixedKeyword .atIdent)

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "!foo" (parsePrefixedKeyword .exclamationIdent)

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "!foo" (parseOptionalPrefixedKeyword .exclamationIdent)

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "#foo" (parsePrefixedKeyword .hashIdent)

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "#foo" (parseOptionalPrefixedKeyword .hashIdent)

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "^foo" (parsePrefixedKeyword .caretIdent)

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "^foo" (parseOptionalPrefixedKeyword .caretIdent)

/--
  info: "Success: [102, 111, 111]"
-/
#guard_msgs in
#eval testParser "%foo" (parsePrefixedKeyword .percentIdent)

/--
  info: "Success: (some [102, 111, 111])"
-/
#guard_msgs in
#eval testParser "%foo" (parseOptionalPrefixedKeyword .percentIdent)

/--
  info: "Error: expected keyword with prefix '@'"
-/
#guard_msgs in
#eval testParser "#foo" (parsePrefixedKeyword .atIdent)

/--
  info: "Success: none"
-/
#guard_msgs in
#eval testParser "#foo" (parseOptionalPrefixedKeyword .atIdent)

end parseList
