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
  Test that parsing a type in the given string returns none in the parseOptional variant,
  and returns the expected error in the parse variant.
-/
def expectMissingType (s : String) : Bool :=
  testOptionalType s = .ok none && (testType s).mapError (·.msg) = .error "type expected"

/--
  Test that parsing an attribute in the given string returns none in the parseOptional variant,
  and returns the expected error in the parse variant.
-/
def expectMissingAttr (s : String) : Bool :=
  testOptionalAttr s = .ok none && (testAttr s).mapError (·.msg) = .error "attribute expected"

/--
  Test that parsing a type in the given string returns the expected error in both variants.
-/
def expectErrorType (s : String) (expected : String)
    (allowUnregisteredDialect : Bool := false) : Bool :=
  (testOptionalType s allowUnregisteredDialect).mapError (·.msg) = .error expected
    && (testType s allowUnregisteredDialect).mapError (·.msg) = .error expected

/--
  Test that parsing an attribute in the given string returns the expected error in both variants.
-/
def expectErrorAttr (s : String) (expected : String)
    (allowUnregisteredDialect : Bool := false) : Bool :=
  (testOptionalAttr s allowUnregisteredDialect).mapError (·.msg) = .error expected
    && (testAttr s allowUnregisteredDialect).mapError (·.msg) = .error expected

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
#assert expectSuccessAttr "false" (IntegerAttr.mk 0 (IntegerType.mk 1))
#assert expectSuccessAttr "true" (IntegerAttr.mk 1 (IntegerType.mk 1))

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
#assert expectErrorAttr "array<>" "integer type expected in dense array attribute"

/-! ## Unregistered dialect type -/

#assert expectSuccessType "!foo.bar" ⟨UnregisteredAttr.mk "!foo.bar" true, by grind⟩ true
#assert expectSuccessType "!foo<bar>" ⟨UnregisteredAttr.mk "!foo<bar>" true, by grind⟩ true
#assert expectSuccessType "!test.test<bar>" ⟨UnregisteredAttr.mk "!test.test<bar>" true, by grind⟩ true

#assert expectErrorType "!foo.bar" "type is not registered. Consider using --allow-unregistered-dialect." false
#assert expectErrorType "!foo<bar>" "type is not registered. Consider using --allow-unregistered-dialect." false
#assert expectErrorType "!test.test<bar>" "type is not registered. Consider using --allow-unregistered-dialect." false


/-! ## Unregistered dialect attribute -/

#assert expectSuccessAttr "#foo<bar>" (UnregisteredAttr.mk "#foo<bar>" false) true
#assert expectSuccessAttr "#test.test<bar>" (UnregisteredAttr.mk "#test.test<bar>" false) true

#assert expectErrorAttr "#foo<bar>" "attribute is not registered. Consider using --allow-unregistered-dialect." false
#assert expectErrorAttr "#test.test<bar>" "attribute is not registered. Consider using --allow-unregistered-dialect." false


/-! ## Location attribute -/

#assert expectSuccessAttr "loc(mysource.cc:10:8)" (LocationAttr.mk "mysource.cc:10:8")
#assert expectSuccessAttr r#"loc(callsite("foo" at "mysource.cc":10:8))"# (LocationAttr.mk r#"callsite("foo" at "mysource.cc":10:8)"#)
#assert expectSuccessAttr r#"loc("mysource.cc":10:8 to 12:18)"# (LocationAttr.mk r#""mysource.cc":10:8 to 12:18"#)
#assert expectSuccessAttr r#"loc(fused["mysource.cc":10:8, "mysource.cc":22:8])"# (LocationAttr.mk r#"fused["mysource.cc":10:8, "mysource.cc":22:8]"#)
#assert expectSuccessAttr r#"loc(fused<CSE>["mysource.cc":10:8, "mysource.cc":22:8])"# (LocationAttr.mk r#"fused<CSE>["mysource.cc":10:8, "mysource.cc":22:8]"#)
#assert expectSuccessAttr r#"loc("CSE"("mysource.cc":10:8))"# (LocationAttr.mk r#""CSE"("mysource.cc":10:8)"#)
#assert expectSuccessAttr "loc(?)" (LocationAttr.mk "?")

/-! ## Modarith type -/

#assert expectSuccessType "!mod_arith.int<17>" (ModArithType.mk 17 none)
#assert expectSuccessType "!mod_arith.int<257 : i32>" (ModArithType.mk 257 (some (IntegerType.mk 32)))
#assert expectSuccessAttr "!mod_arith.int<17>" (ModArithType.mk 17 none)
#assert expectErrorType "!mod_arith.int<>" "modarith type modulus expected"
#assert expectErrorType "!mod_arith.int<17 : x>" "integer type expected after ':' in modarith type"

/-! ## LLVM Pointer type -/
#assert expectSuccessType "!llvm.ptr" (LLVM.PointerType.mk)

/-! ## LLVM Array type -/
#assert expectSuccessType "!llvm.array<2 x i32>" (LLVM.ArrayType.mk 2 $ IntegerType.mk 32)
#assert expectSuccessAttr "!llvm.array<2 x !llvm.array<3x i64>>" (LLVM.ArrayType.mk 2 $ LLVM.ArrayType.mk 3 $ IntegerType.mk 64)

/-! ## LLVM Function type -/
#assert expectSuccessType "!llvm.func<i32 (i32)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(IntegerType.mk 32 : Attribute)] #[(IntegerType.mk 32 : Attribute)]), by rfl⟩
#assert expectSuccessType "!llvm.func<i64 ()>"
  ⟨.llvmFunctionType (FunctionType.mk #[] #[(IntegerType.mk 64 : Attribute)]), by rfl⟩
#assert expectSuccessType "!llvm.func<i32 (i32, i64)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(IntegerType.mk 32 : Attribute), (IntegerType.mk 64 : Attribute)]
    #[(IntegerType.mk 32 : Attribute)]), by rfl⟩
#assert expectSuccessType "!llvm.func<!llvm.ptr (!llvm.ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute)] #[(LLVM.PointerType.mk : Attribute)]), by rfl⟩
-- LLVM pretty-print sugar: bare `void` and `ptr` keywords inside `!llvm.func<...>`.
#assert expectSuccessType "!llvm.func<void ()>"
  ⟨.llvmFunctionType (FunctionType.mk #[]
    #[(UnregisteredAttr.mk "!llvm.void" true : Attribute)]), by rfl⟩
#assert expectSuccessType "!llvm.func<void (i32)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(IntegerType.mk 32 : Attribute)]
    #[(UnregisteredAttr.mk "!llvm.void" true : Attribute)]), by rfl⟩
#assert expectSuccessType "!llvm.func<i32 (ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute)] #[(IntegerType.mk 32 : Attribute)]), by rfl⟩
#assert expectSuccessType "!llvm.func<void (ptr, ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute), (LLVM.PointerType.mk : Attribute)]
    #[(UnregisteredAttr.mk "!llvm.void" true : Attribute)]), by rfl⟩
-- Bare sugar mixed with the explicit `!llvm.ptr` form within one function type.
#assert expectSuccessType "!llvm.func<void (!llvm.ptr, ptr)>"
  ⟨.llvmFunctionType (FunctionType.mk
    #[(LLVM.PointerType.mk : Attribute), (LLVM.PointerType.mk : Attribute)]
    #[(UnregisteredAttr.mk "!llvm.void" true : Attribute)]), by rfl⟩

/-! ## CUDA Pointer type -/
#assert expectSuccessType "!cuda_tile.ptr<i1>" (CudaTile.PointerType.mk (IntegerType.mk 1))
#assert expectSuccessType "!cuda_tile.ptr<i32>" (CudaTile.PointerType.mk (IntegerType.mk 32))
#assert expectErrorType "!cuda_tile.ptr<16>" "integer type expected"

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
#assert expectErrorType "!hw.modty<foo>" "module port expected"
#assert expectErrorType "!hw.modty<input : foo>" "identifier expected"
#assert expectErrorType "!hw.modty<input a : foo>" "integer type expected"
