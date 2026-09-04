import Veir.Parser.AttrParser
import Veir.IR.Basic

open Veir
open Veir.Parser
open Veir.Parser.ParserError
open Veir.AttrParser
open Veir.Attribute

/--
  Run parseOptionalType on the given input string.
-/
def testOptionalType (s : String) (allowUnregisteredDialect : Bool := false) :
    Except ParserError (Option TypeAttr) := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseOptionalType.run' { allowUnregisteredDialect } parser

/--
  Run parseType on the given input string.
-/
def testType (s : String) (allowUnregisteredDialect : Bool := false) :
    Except ParserError TypeAttr := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseType.run' { allowUnregisteredDialect } parser

/-- Build the alias map of an `AttrParserState` from `(name, type)` pairs. -/
def aliasMap (aliases : List (String × TypeAttr)) : Std.HashMap ByteArray TypeAttr :=
  aliases.foldl (fun map (name, type) => map.insert name.toByteArray type) {}

/--
  Run parseType on the given input string with the given type aliases in scope.
-/
def testTypeWithAliases (s : String) (aliases : List (String × TypeAttr))
    (allowUnregisteredDialect : Bool := false) : Except ParserError TypeAttr := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseType.run' { allowUnregisteredDialect, typeAliases := aliasMap aliases } parser

/--
  Run parseAttribute on the given input string with the given type aliases in scope.
-/
def testAttrWithAliases (s : String) (aliases : List (String × TypeAttr))
    (allowUnregisteredDialect : Bool := false) : Except ParserError Attribute := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseAttribute.run' { allowUnregisteredDialect, typeAliases := aliasMap aliases } parser

/--
  Run parseOptionalAttr on the given input string.
-/
def testOptionalAttr (s : String) (allowUnregisteredDialect : Bool := false) :
    Except ParserError (Option Attribute) := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseOptionalAttribute.run' { allowUnregisteredDialect } parser

/--
  Run parseType on the given input string.
-/
def testAttr (s : String) (allowUnregisteredDialect : Bool := false) :
    Except ParserError Attribute := do
  let parser ← ParserState.fromInput (s.toByteArray)
  parseAttribute.run' { allowUnregisteredDialect } parser

/--
  Test that parsing a type in the given string succeeds and matches the expected type.
-/
def expectSuccessType (s : String) (expected : TypeAttr)
    (allowUnregisteredDialect : Bool := false) : Bool :=
  testOptionalType s allowUnregisteredDialect = .ok (some expected) ∧
  testType s allowUnregisteredDialect = .ok expected

/--
  Test that parsing an attribute in the given string succeeds and matches the expected attribute.
-/
def expectSuccessAttr (s : String) (expected : Attribute)
    (allowUnregisteredDialect : Bool := false) : Bool :=
  testOptionalAttr s allowUnregisteredDialect = .ok (some expected) ∧
  testAttr s allowUnregisteredDialect = .ok expected

/--
  Extract the message and byte offset of a parser error, so tests can assert
  both the message and the source location.
-/
def errorInfo (e : ParserError) : String × Option Nat :=
  (e.msg, e.pos.map (·.byteOffset))

/--
  Test that parsing a type in the given string returns none in the parseOptional variant,
  and returns the expected error and byte offset in the parse variant.
-/
def expectMissingType (s : String) : Bool :=
  testOptionalType s = .ok none
    && (testType s).mapError errorInfo = .error ("type expected", some 0)

/--
  Test that parsing an attribute in the given string returns none in the parseOptional variant,
  and returns the expected error and byte offset in the parse variant.
-/
def expectMissingAttr (s : String) : Bool :=
  testOptionalAttr s = .ok none
    && (testAttr s).mapError errorInfo = .error ("attribute expected", some 0)

/--
  Test that parsing a type in the given string returns the expected error and byte offset
  in both variants.
-/
def expectErrorType (s : String) (expected : String) (pos : Option Nat)
    (allowUnregisteredDialect : Bool := false) : Bool :=
  (testOptionalType s allowUnregisteredDialect).mapError errorInfo = .error (expected, pos)
    && (testType s allowUnregisteredDialect).mapError errorInfo = .error (expected, pos)

/--
  Test that parsing an attribute in the given string returns the expected error and byte offset
  in both variants.
-/
def expectErrorAttr (s : String) (expected : String) (pos : Option Nat)
    (allowUnregisteredDialect : Bool := false) : Bool :=
  (testOptionalAttr s allowUnregisteredDialect).mapError errorInfo = .error (expected, pos)
    && (testAttr s allowUnregisteredDialect).mapError errorInfo = .error (expected, pos)

/--
  Test that parsing an attribute and printing it back reproduces the input text exactly.
-/
def expectRoundTripAttr (s : String) (allowUnregisteredDialect : Bool := false) : Bool :=
  (testAttr s allowUnregisteredDialect).map Attribute.toString = .ok s

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

#assert expectErrorType "\"" "expected '\"' in string literal" none
#assert expectMissingType "foo"
#assert expectMissingAttr "i0x4"

/-! ## Integer types -/

#assert expectSuccessType "i32" (IntegerType.mk 32)
#assert expectSuccessType "i0" (IntegerType.mk 0)
#assert expectMissingType "i0x4"

/-! ## Types parsed as attributes -/

#assert expectSuccessAttr "i32" (IntegerType.mk 32)

/-! ## Vector types -/

#assert expectSuccessType "vector<4xi32>" (VectorType.mk #[4] (IntegerType.mk 32))
#assert expectSuccessType "vector<2x4xf64>" (VectorType.mk #[2, 4] (FloatType.mk 64))
#assert expectSuccessType "vector<2 x 4 x i32>" (VectorType.mk #[2, 4] (IntegerType.mk 32))
#assert expectSuccessType "vector<i32>" (VectorType.mk #[] (IntegerType.mk 32))
#assert expectSuccessAttr "vector<4xi32>" (VectorType.mk #[4] (IntegerType.mk 32))
#assert ToString.toString (VectorType.mk #[2, 4] (IntegerType.mk 32) : VectorType) ==
  "vector<2x4xi32>"
#assert ToString.toString (VectorType.mk #[] (IntegerType.mk 32) : VectorType) == "vector<i32>"
#assert expectErrorType "vector<4x>" "vector element type expected" (some 9)
#assert expectErrorType "vector<0xi32>" "0 is not a supported dimension" (some 7)
#assert expectErrorType "vector<0x32xi32>" "0 is not a supported dimension" (some 7)

/-! ## Integer attributes -/

#assert expectErrorAttr "0 : 2" "integer type expected after ':' in integer attribute" (some 4)
#assert expectSuccessAttr "0 : i32" (IntegerAttr.mk 0 (IntegerType.mk 32))
#assert expectSuccessAttr "false" (IntegerAttr.mk 0 (IntegerType.mk 1))
#assert expectSuccessAttr "true" (IntegerAttr.mk 1 (IntegerType.mk 1))

/-! ## Integer overflow flags attributes -/

#assert expectSuccessAttr "#arith.overflow<none>" (ArithIntegerOverflowFlagsAttr.mk false false)
#assert expectSuccessAttr "#arith.overflow<nsw>" (ArithIntegerOverflowFlagsAttr.mk true false)
#assert expectSuccessAttr "#arith.overflow<nuw>" (ArithIntegerOverflowFlagsAttr.mk false true)
#assert expectSuccessAttr "#arith.overflow<nsw, nuw>" (ArithIntegerOverflowFlagsAttr.mk true true)
#assert expectErrorAttr "#arith.overflow<>"
  "expected integer overflow flag to be one of: none, nsw, nuw" (some 16)

/-! ## String attributes -/

#assert expectSuccessAttr "\"hello\"" (StringAttr.mk "hello".toByteArray)
#assert expectSuccessAttr "\"\"" (StringAttr.mk "".toByteArray)
#assert expectSuccessAttr "\"\\\"\"" (StringAttr.mk "\"".toByteArray)
#assert expectSuccessAttr "\"hello world\"" (StringAttr.mk "hello world".toByteArray)
#assert expectMissingAttr "hello"  -- bare identifier, not a string attribute

/-! ## Unit attribute -/

#assert expectSuccessAttr "unit" (UnitAttr.mk)
#assert expectMissingAttr "foo"

/-! ## Dictionary attribute -/

#assert expectSuccessAttr "{}" (DictionaryAttr.mk #[])
#assert expectSuccessAttr "{ foo = \"hello\" }"
  (DictionaryAttr.mk #[("foo".toByteArray, StringAttr.mk "hello".toByteArray)])
#assert expectSuccessAttr "{x}" (DictionaryAttr.mk #[("x".toByteArray, UnitAttr.mk)])
#assert expectSuccessAttr "{ a, b }"
  (DictionaryAttr.mk #[("a".toByteArray, UnitAttr.mk), ("b".toByteArray, UnitAttr.mk)])
/- Test unsorted keys -/
#assert expectSuccessAttr "{ b = unit, a = \"hello\" }"
  (DictionaryAttr.mk #[("a".toByteArray, StringAttr.mk "hello".toByteArray), ("b".toByteArray, UnitAttr.mk)])

/-! ## Array attribute -/

#assert expectSuccessAttr "[]" (ArrayAttr.mk #[])
#assert expectSuccessAttr "[unit]" (ArrayAttr.mk #[UnitAttr.mk])
#assert expectSuccessAttr "[1 : i32, \"foo\"]"
  (ArrayAttr.mk #[IntegerAttr.mk 1 (IntegerType.mk 32), StringAttr.mk "foo".toByteArray])
#assert expectSuccessAttr "[[]]" (ArrayAttr.mk #[ArrayAttr.mk #[]])

/-! ## Dense array attribute -/

#assert expectSuccessAttr "array<i8>" (DenseArrayAttr.mk (IntegerType.mk 8) #[])
#assert expectSuccessAttr "array<i32: 10, 42>" (DenseArrayAttr.mk (IntegerType.mk 32) #[10, 42])
#assert expectSuccessAttr "array<i64: -1>" (DenseArrayAttr.mk (IntegerType.mk 64) #[-1])
#assert expectSuccessAttr "array<i16: 0>" (DenseArrayAttr.mk (IntegerType.mk 16) #[0])
#assert expectErrorAttr "array<>" "integer type expected in dense array attribute" (some 6)

/-! ## Dense elements attribute -/

#assert expectSuccessAttr "dense<0> : tensor<4xi8>" (DenseElementsAttr.mk "0" "tensor<4xi8>")
#assert expectSuccessAttr "dense<0> : vector<4xi8>" (DenseElementsAttr.mk "0" "vector<4xi8>")
#assert expectSuccessAttr "dense<[32, 64]> : vector<2xi64>"
  (DenseElementsAttr.mk "[32, 64]" "vector<2xi64>")
#assert expectSuccessAttr "dense<0> : vector<[4]xi8>" (DenseElementsAttr.mk "0" "vector<[4]xi8>")
#assert expectErrorAttr "dense<0> : memref<4xi8>"
  "'tensor' or 'vector' type expected in dense elements attribute" (some 11)

/-! ## Unregistered dialect type -/

#assert expectSuccessType "!foo.bar" ⟨UnregisteredAttr.mk "!foo.bar" true none, by grind⟩ true
#assert expectSuccessType "!foo<bar>" ⟨UnregisteredAttr.mk "!foo<bar>" true none, by grind⟩ true
#assert expectSuccessType "!test.test<bar>" ⟨UnregisteredAttr.mk "!test.test<bar>" true none, by grind⟩ true

#assert expectErrorType "!foo.bar" "type '!foo.bar' is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorType "!foo<bar>" "type '!foo' is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorType "!test.test<bar>" "type '!test.test' is not registered. Consider using --allow-unregistered-dialect." (some 0) false


/-! ## Type aliases -/

-- An alias resolves to its definition and needs no unregistered-dialect flag.
#assert (testTypeWithAliases "!int" [("int", IntegerType.mk 32)] = .ok (IntegerType.mk 32))
#assert (testTypeWithAliases "!int" [("int", IntegerType.mk 32)] true = .ok (IntegerType.mk 32))
-- Aliases resolve inside compound types.
#assert (testTypeWithAliases "!llvm.array<2 x !int>" [("int", IntegerType.mk 32)]
  = .ok (LLVM.ArrayType.mk 2 (IntegerType.mk 32 : Attribute)))
#assert ((testTypeWithAliases "(!int) -> !int" [("int", IntegerType.mk 32)]).map (·.val)
  = .ok (.functionType (FunctionType.mk #[(IntegerType.mk 32 : Attribute)]
      #[(IntegerType.mk 32 : Attribute)] (isVarArg := false))))
-- An alias may stand for a dialect type.
#assert (testTypeWithAliases "!p" [("p", LLVM.PointerType.mk)] = .ok LLVM.PointerType.mk)
-- An undefined alias is an error whether or not unregistered dialects are allowed.
#assert ((testTypeWithAliases "!int" []).mapError errorInfo
  = .error ("undefined symbol alias id 'int'", some 0))
#assert ((testTypeWithAliases "!int" [] true).mapError errorInfo
  = .error ("undefined symbol alias id 'int'", some 0))
-- A dialect dot or an adjacent body is a dialect type, not an alias; rejected here as unregistered.
#assert ((testTypeWithAliases "!foo.bar" [("foo", IntegerType.mk 32)]).mapError errorInfo
  = .error ("type '!foo.bar' is not registered. Consider using --allow-unregistered-dialect.", some 0))
#assert ((testTypeWithAliases "!foo<bar>" [("foo", IntegerType.mk 32)]).mapError errorInfo
  = .error ("type '!foo' is not registered. Consider using --allow-unregistered-dialect.", some 0))
#assert ((testTypeWithAliases "!foo <bar>" [] true).mapError errorInfo
  = .error ("undefined symbol alias id 'foo'", some 0))
-- Aliases also resolve where a specific builtin type is required.
#assert (testAttrWithAliases "1 : !int" [("int", IntegerType.mk 32)]
  = .ok (IntegerAttr.mk 1 (IntegerType.mk 32)))
#assert (testAttrWithAliases "array<!int: 1, 2>" [("int", IntegerType.mk 32)]
  = .ok (DenseArrayAttr.mk (IntegerType.mk 32) #[1, 2]))
#assert (testTypeWithAliases "!cuda_tile.ptr<!int>" [("int", IntegerType.mk 32)]
  = .ok (CudaTile.PointerType.mk (IntegerType.mk 32)))
#assert (testTypeWithAliases "!hw.modty<input a : !int>" [("int", IntegerType.mk 32)]
  = .ok (HW.ModuleType.mk #[{ dir := .input, name := "a", type := IntegerType.mk 32 }]))
-- An alias for another kind of type is rejected at the alias with the position's own message.
#assert ((testAttrWithAliases "array<!p: 1>" [("p", LLVM.PointerType.mk)]).mapError errorInfo
  = .error ("integer type expected in dense array attribute", some 6))
#assert ((testAttrWithAliases "1 : !p" [("p", LLVM.PointerType.mk)]).mapError errorInfo
  = .error ("integer type expected after ':' in integer attribute", some 4))

/-! ## Unregistered dialect attribute -/

#assert expectSuccessAttr "#foo<bar>" (UnregisteredAttr.mk "#foo<bar>" false none) true
#assert expectSuccessAttr "#test.test<bar>" (UnregisteredAttr.mk "#test.test<bar>" false none) true
#assert expectSuccessAttr "#foo.bar" (UnregisteredAttr.mk "#foo.bar" false none) true
#assert expectSuccessAttr "#foo.bar<baz> : i32"
  (UnregisteredAttr.mk "#foo.bar<baz>" false (some (IntegerType.mk 32 : Attribute))) true
#assert expectSuccessAttr "#foo.zero : !foo.ty"
  (UnregisteredAttr.mk "#foo.zero" false (some (UnregisteredAttr.mk "!foo.ty" true none : Attribute))) true
#assert expectSuccessAttr "#foo.int<1> : !foo.int<s, 32>"
  (UnregisteredAttr.mk "#foo.int<1>" false
    (some (UnregisteredAttr.mk "!foo.int<s, 32>" true none : Attribute))) true
#assert expectSuccessAttr "#foo.bar<1> : !foo.ptr<!foo.int<s, 32>>"
  (UnregisteredAttr.mk "#foo.bar<1>" false
    (some (UnregisteredAttr.mk "!foo.ptr<!foo.int<s, 32>>" true none : Attribute))) true
#assert expectSuccessAttr "#foo<bar> : i1"
  (UnregisteredAttr.mk "#foo<bar>" false (some (IntegerType.mk 1 : Attribute))) true
#assert expectSuccessAttr "#foo.bar : (i32) -> i32"
  (UnregisteredAttr.mk "#foo.bar" false (some (.functionType
    (FunctionType.mk #[(IntegerType.mk 32 : Attribute)] #[(IntegerType.mk 32 : Attribute)]
      (isVarArg := false))))) true
-- A `:` must be followed by a type.
#assert expectErrorAttr "#foo.bar<baz> :" "type expected" (some 15) true
#assert expectErrorAttr "#foo.bar : 5" "type expected" (some 11) true
-- The flag is still required when the attribute has no body or carries a type.
#assert expectErrorAttr "#foo.bar" "attribute '#foo.bar' is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorAttr "#foo.bar<baz> : i32" "attribute '#foo.bar' is not registered. Consider using --allow-unregistered-dialect." (some 0) false
-- Printing reproduces the source text, with the trailing type after the body.
#assert expectRoundTripAttr "#foo.bar" true
#assert expectRoundTripAttr "#foo.bar<baz>" true
#assert expectRoundTripAttr "#foo.bar<baz> : i32" true
#assert expectRoundTripAttr "#foo.zero : !foo.ptr<!foo.int<s, 32>>" true
-- Equality takes the trailing type into account.
#assert (UnregisteredAttr.mk "#foo.bar" false (some (IntegerType.mk 32 : Attribute))
  = UnregisteredAttr.mk "#foo.bar" false (some (IntegerType.mk 32 : Attribute)))
#assert (UnregisteredAttr.mk "#foo.bar" false (some (IntegerType.mk 32 : Attribute))
  ≠ UnregisteredAttr.mk "#foo.bar" false none)
#assert (UnregisteredAttr.mk "#foo.bar" false (some (IntegerType.mk 32 : Attribute))
  ≠ UnregisteredAttr.mk "#foo.bar" false (some (IntegerType.mk 64 : Attribute)))

#assert expectErrorAttr "#foo<bar>" "attribute '#foo' is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorAttr "#test.test<bar>" "attribute '#test.test' is not registered. Consider using --allow-unregistered-dialect." (some 0) false


/-! ## Location attribute -/

#assert expectSuccessAttr "loc(mysource.cc:10:8)" (LocationAttr.mk "mysource.cc:10:8")
#assert expectSuccessAttr r#"loc(callsite("foo" at "mysource.cc":10:8))"# (LocationAttr.mk r#"callsite("foo" at "mysource.cc":10:8)"#)
#assert expectSuccessAttr r#"loc("mysource.cc":10:8 to 12:18)"# (LocationAttr.mk r#""mysource.cc":10:8 to 12:18"#)
#assert expectSuccessAttr r#"loc(fused["mysource.cc":10:8, "mysource.cc":22:8])"# (LocationAttr.mk r#"fused["mysource.cc":10:8, "mysource.cc":22:8]"#)
#assert expectSuccessAttr r#"loc(fused<CSE>["mysource.cc":10:8, "mysource.cc":22:8])"# (LocationAttr.mk r#"fused<CSE>["mysource.cc":10:8, "mysource.cc":22:8]"#)
#assert expectSuccessAttr r#"loc("CSE"("mysource.cc":10:8))"# (LocationAttr.mk r#""CSE"("mysource.cc":10:8)"#)
#assert expectSuccessAttr "loc(?)" (LocationAttr.mk "?")

/-! ## Modarith type -/

#assert expectSuccessType "!mod_arith.int<17 : i64>" (ModArithType.mk (IntegerAttr.mk 17 (IntegerType.mk 64)))
#assert expectSuccessType "!mod_arith.int<257 : i32>" (ModArithType.mk (IntegerAttr.mk 257 (IntegerType.mk 32)))
#assert expectSuccessAttr "!mod_arith.int<17 : i64>" (ModArithType.mk (IntegerAttr.mk 17 (IntegerType.mk 64)))
#assert expectErrorType "!mod_arith.int<>" "modarith type modulus expected" (some 15)
#assert expectErrorType "!mod_arith.int<17>" "Expected punctuation ':'" (some 17)
#assert expectErrorType "!mod_arith.int<17 : x>" "integer type expected after ':' in integer attribute" (some 20)

/-! ## ClangIR types -/

#assert expectSuccessType "!cir.int<s, 32>" (CirIntType.mk true 32)
#assert expectSuccessType "!cir.int<u, 8>" (CirIntType.mk false 8)
#assert expectSuccessAttr "!cir.int<s, 32>" (CirIntType.mk true 32)
#assert expectSuccessType "!cir.bool" (CirBoolType.mk)
#assert expectSuccessType "!cir.func<()>" (CirFuncType.mk (FunctionType.mk #[] #[] false))
#assert expectSuccessType "!cir.func<(!cir.int<s, 32>, !cir.bool) -> !cir.int<s, 32>>"
  (CirFuncType.mk (FunctionType.mk
    #[(CirIntType.mk true 32 : Attribute), (CirBoolType.mk : Attribute)]
    #[(CirIntType.mk true 32 : Attribute)] false))
#assert expectSuccessType "!cir.func<(!cir.int<s, 32>, ...) -> !cir.int<s, 32>>"
  (CirFuncType.mk (FunctionType.mk
    #[(CirIntType.mk true 32 : Attribute)] #[(CirIntType.mk true 32 : Attribute)] true))
#assert expectErrorType "!cir.int<x, 32>" "cir.int signedness expected ('s' or 'u')" (some 9)
#assert expectErrorType "!cir.int<s>" "Expected punctuation ','" (some 10)
#assert expectErrorType "!cir.int<s, 0>" "cir.int bitwidth must be positive" (some 13)

/-! ## ClangIR attributes -/

#assert expectSuccessAttr "#cir.int<42> : !cir.int<s, 32>" (CirIntAttr.mk 42 (CirIntType.mk true 32))
#assert expectSuccessAttr "#cir.int<-1> : !cir.int<s, 8>" (CirIntAttr.mk (-1) (CirIntType.mk true 8))
#assert expectSuccessAttr "#cir.bool<true> : !cir.bool" (CirBoolAttr.mk true)
#assert expectSuccessAttr "#cir.bool<false> : !cir.bool" (CirBoolAttr.mk false)
#assert expectErrorAttr "#cir.int<42>" "Expected punctuation ':'" (some 12)
#assert expectErrorAttr "#cir.int<42> : i32" "#cir.int<N> expects a !cir.int type annotation" (some 15)

/-! ## PDL handle types -/
#assert expectSuccessType "!pdl.attribute" (PDL.AttributeType.mk)
#assert expectSuccessType "!pdl.range<value>" (PDL.RangeType.mk .value)
#assert expectSuccessType "!pdl.range<attribute>" (PDL.RangeType.mk .attribute)
#assert expectSuccessAttr "!pdl.attribute" (PDL.AttributeType.mk)

#assert expectSuccessType "!pdl.operation" (PDL.OperationType.mk)
#assert expectSuccessAttr "!pdl.operation" (PDL.OperationType.mk)

#assert expectSuccessType "!pdl.value" (PDL.ValueType.mk)
#assert expectSuccessAttr "!pdl.value" (PDL.ValueType.mk)

#assert expectSuccessType "!pdl.type" (PDL.TypeType.mk)
#assert expectSuccessAttr "!pdl.type" (PDL.TypeType.mk)

/-! ## LLVM Pointer type -/
#assert expectSuccessType "!llvm.ptr" (LLVM.PointerType.mk)

/-! ## LLVM Void type -/
#assert expectSuccessType "!llvm.void" (LLVM.VoidType.mk)

/-! ## LLVM Array type -/
#assert expectSuccessType "!llvm.array<2 x i32>" (LLVM.ArrayType.mk 2 $ IntegerType.mk 32)
#assert expectSuccessAttr "!llvm.array<2 x !llvm.array<3x i64>>" (LLVM.ArrayType.mk 2 $ LLVM.ArrayType.mk 3 $ IntegerType.mk 64)

/-! ## LLVM Byte type -/
#assert expectSuccessType "!llvm.byte<64>" (LLVM.ByteType.mk 64)

/-! ## LLVM Struct type (parsed opaquely; see `parseOptionalLLVMStructType`)

  The struct type is handled by a dedicated parser that accepts both the
  standalone `!llvm.struct<...>` form and the bare `struct<...>` form used when a
  struct is nested inside another LLVM type (e.g. an array element). Both forms
  are normalized to the full `!llvm.struct<...>` spelling, and neither requires
  `allowUnregisteredDialect` (like `!llvm.array`). The struct name, fields, and
  packed flag are *not* modeled structurally — they survive only as text. -/

-- Standalone struct: both forms parse identically, with or without the flag.
#assert expectSuccessType "!llvm.struct<(i32, f32)>"
  ⟨UnregisteredAttr.mk "!llvm.struct<(i32, f32)>" true none, by grind⟩ false
#assert expectSuccessType "!llvm.struct<(i32, f32)>"
  ⟨UnregisteredAttr.mk "!llvm.struct<(i32, f32)>" true none, by grind⟩ true
-- Literal struct nested in an array (original `!llvm.array<N x struct<...>>` bug).
#assert expectSuccessType "!llvm.array<2 x struct<(i32, f32)>>"
  (LLVM.ArrayType.mk 2 (UnregisteredAttr.mk "!llvm.struct<(i32, f32)>" true none : Attribute)) true
#assert expectSuccessType "!llvm.array<2 x struct<(i32, f32)>>"
  (LLVM.ArrayType.mk 2 (UnregisteredAttr.mk "!llvm.struct<(i32, f32)>" true none : Attribute)) false
-- The bare nested form and the prefixed nested form are equivalent.
#assert expectSuccessType "!llvm.array<2 x !llvm.struct<(i32, f32)>>"
  (LLVM.ArrayType.mk 2 (UnregisteredAttr.mk "!llvm.struct<(i32, f32)>" true none : Attribute)) false
-- Identified (named) struct: the name is preserved verbatim inside the text.
#assert expectSuccessType "!llvm.array<23 x struct<\"struct.et_info\", (i8, i8)>>"
  (LLVM.ArrayType.mk 23
    (UnregisteredAttr.mk "!llvm.struct<\"struct.et_info\", (i8, i8)>" true none : Attribute)) true
-- Packed struct nested in an array.
#assert expectSuccessType "!llvm.array<4 x struct<packed (i8, i32)>>"
  (LLVM.ArrayType.mk 4 (UnregisteredAttr.mk "!llvm.struct<packed (i8, i32)>" true none : Attribute)) true

/-! ## LLVM Function type -/
#assert expectSuccessType "!llvm.func<i32 (i32)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(IntegerType.mk 32 : Attribute)] #[(IntegerType.mk 32 : Attribute)] (isVarArg := false)), by rfl⟩
#assert expectSuccessType "!llvm.func<i64 ()>"
  ⟨.llvmFunctionType (FunctionType.mk #[] #[(IntegerType.mk 64 : Attribute)] (isVarArg := false)), by rfl⟩
#assert expectSuccessType "!llvm.func<i32 (i32, i64)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(IntegerType.mk 32 : Attribute), (IntegerType.mk 64 : Attribute)]
    #[(IntegerType.mk 32 : Attribute)] (isVarArg := false)), by rfl⟩
#assert expectSuccessType "!llvm.func<!llvm.ptr (!llvm.ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute)] #[(LLVM.PointerType.mk : Attribute)] (isVarArg := false)), by rfl⟩
-- LLVM pretty-print sugar: bare `void` and `ptr` keywords inside `!llvm.func<...>`.
#assert expectSuccessType "!llvm.func<void ()>"
  ⟨.llvmFunctionType (FunctionType.mk #[]
    #[(LLVM.VoidType.mk : Attribute)] (isVarArg := false)), by rfl⟩
#assert expectSuccessType "!llvm.func<void (i32)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(IntegerType.mk 32 : Attribute)]
    #[(LLVM.VoidType.mk : Attribute)] (isVarArg := false)), by rfl⟩
#assert expectSuccessType "!llvm.func<i32 (ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute)] #[(IntegerType.mk 32 : Attribute)] (isVarArg := false)), by rfl⟩
#assert expectSuccessType "!llvm.func<void (ptr, ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute), (LLVM.PointerType.mk : Attribute)]
    #[(LLVM.VoidType.mk : Attribute)] (isVarArg := false)), by rfl⟩
-- Bare sugar mixed with the explicit `!llvm.ptr` form within one function type.
#assert expectSuccessType "!llvm.func<void (!llvm.ptr, ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute), (LLVM.PointerType.mk : Attribute)]
    #[(LLVM.VoidType.mk : Attribute)] (isVarArg := false)), by rfl⟩
-- Variadic function types: a trailing `...`, with or without fixed parameters.
#assert expectSuccessType "!llvm.func<i32 (ptr, ...)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute)] #[(IntegerType.mk 32 : Attribute)] (isVarArg := true)), by rfl⟩
#assert expectSuccessType "!llvm.func<i32 (...)>"
  ⟨.llvmFunctionType (FunctionType.mk #[] #[(IntegerType.mk 32 : Attribute)] (isVarArg := true)), by rfl⟩

/-! ## LLVM calling convention and linkage attributes -/
#assert expectSuccessAttr "#llvm.cconv<ccc>" (CConvAttr.mk "ccc")
#assert expectSuccessAttr "#llvm.cconv<fastcc>" (CConvAttr.mk "fastcc")
#assert expectSuccessAttr "#llvm.linkage<external>" (LinkageAttr.mk "external")
#assert expectSuccessAttr "#llvm.linkage<internal>" (LinkageAttr.mk "internal")
#assert expectSuccessAttr "#llvm.tailcallkind<none>" (TailCallKindAttr.mk "none")
#assert expectSuccessAttr "#llvm.tailcallkind<musttail>" (TailCallKindAttr.mk "musttail")

/-! ## LLVM constant ranges -/
#assert expectSuccessAttr "#llvm.constant_range<i32, 0, 19>"
  (ConstantRangeAttr.mk "i32, 0, 19")
-- A wrapping range: LLVM allows `hi < lo`, and the bound reads back negative.
#assert expectSuccessAttr "#llvm.constant_range<i32, 0, -7>"
  (ConstantRangeAttr.mk "i32, 0, -7")

/-! ## LLVM TBAA tags -/
#assert expectSuccessAttr
  "#llvm.tbaa_tag<base_type = <id = \"int\">, access_type = <id = \"int\">, offset = 0>"
  (TbaaTagAttr.mk "base_type = <id = \"int\">, access_type = <id = \"int\">, offset = 0")
#assert expectSuccessAttr
  "#llvm.tbaa_tag<base_type = <id = \"a\", members = {<#llvm.tbaa_root<id = \"r\">, 0>}>, offset = 8>"
  (TbaaTagAttr.mk "base_type = <id = \"a\", members = {<#llvm.tbaa_root<id = \"r\">, 0>}>, offset = 8")

/-! ## LLVM memory effects -/
#assert expectSuccessAttr
  "#llvm.memory_effects<other = none, argMem = read, inaccessibleMem = none>"
  (MemoryEffectsAttr.mk "other = none, argMem = read, inaccessibleMem = none")
-- The LLVM 22 spelling: three more location classes than the original three.
#assert expectSuccessAttr
  "#llvm.memory_effects<other = readwrite, argMem = readwrite, inaccessibleMem = none, \
    errnoMem = readwrite, targetMem0 = none, targetMem1 = none>"
  (MemoryEffectsAttr.mk "other = readwrite, argMem = readwrite, inaccessibleMem = none, \
    errnoMem = readwrite, targetMem0 = none, targetMem1 = none")

/-! ## CUDA Pointer type -/
#assert expectSuccessType "!cuda_tile.ptr<i1>" (CudaTile.PointerType.mk (IntegerType.mk 1))
#assert expectSuccessType "!cuda_tile.ptr<i32>" (CudaTile.PointerType.mk (IntegerType.mk 32))
#assert expectErrorType "!cuda_tile.ptr<16>" "integer type expected" (some 15)
-- A `!cuda_tile.ptr<...>` may appear as a (parenthesized) function-type input. See #675.
#assert expectSuccessType "(!cuda_tile.ptr<i1>) -> ()"
  (FunctionType.mk #[(CudaTile.PointerType.mk (IntegerType.mk 1) : Attribute)] #[] (isVarArg := false))
#assert expectSuccessType "!io.address" Io.AddressType.mk
#assert expectSuccessType "(!io.address) -> ()"
  (FunctionType.mk #[(Io.AddressType.mk : Attribute)] #[] (isVarArg := false))

/-! ## RISCV Register type -/
#assert expectSuccessType "!riscv.reg" (RegisterType.mk)
#assert expectSuccessType "!riscv.reg<x13>" (RegisterType.mk (some 13))

/-! ## Flat symbol reference attribute -/
#assert expectSuccessAttr "@foo" (FlatSymbolRefAttr.mk "@foo")
#assert expectSuccessAttr "@printf" (FlatSymbolRefAttr.mk "@printf")
#assert expectSuccessAttr "@\"my.func\"" (FlatSymbolRefAttr.mk "@\"my.func\"")
#assert expectMissingAttr "foo"

/-! ## HW Module type -/
#assert expectSuccessType "!hw.modty<>" (HW.ModuleType.mk #[])
#assert expectSuccessType "!hw.modty<input a : i3, inout b : i6,  output c : i10>"
  (HW.ModuleType.mk #[
    {name := "a", type := IntegerType.mk 3, dir := .input},
    {name := "b", type := IntegerType.mk 6, dir := .inout},
    {name := "c", type := IntegerType.mk 10, dir := .output}])
#assert expectErrorType "!hw.modty<foo>" "module port expected" (some 10)
#assert expectErrorType "!hw.modty<input : foo>" "identifier expected" (some 16)
#assert expectErrorType "!hw.modty<input a : foo>" "integer type expected" (some 20)
