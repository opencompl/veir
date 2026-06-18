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

/-! ## Unregistered dialect type -/

#assert expectSuccessType "!foo.bar" ⟨UnregisteredAttr.mk "!foo.bar" true, by grind⟩ true
#assert expectSuccessType "!foo<bar>" ⟨UnregisteredAttr.mk "!foo<bar>" true, by grind⟩ true
#assert expectSuccessType "!test.test<bar>" ⟨UnregisteredAttr.mk "!test.test<bar>" true, by grind⟩ true

#assert expectErrorType "!foo.bar" "type is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorType "!foo<bar>" "type is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorType "!test.test<bar>" "type is not registered. Consider using --allow-unregistered-dialect." (some 0) false


/-! ## Unregistered dialect attribute -/

#assert expectSuccessAttr "#foo<bar>" (UnregisteredAttr.mk "#foo<bar>" false) true
#assert expectSuccessAttr "#test.test<bar>" (UnregisteredAttr.mk "#test.test<bar>" false) true

#assert expectErrorAttr "#foo<bar>" "attribute is not registered. Consider using --allow-unregistered-dialect." (some 0) false
#assert expectErrorAttr "#test.test<bar>" "attribute is not registered. Consider using --allow-unregistered-dialect." (some 0) false


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

/-! ## LLVM Pointer type -/
#assert expectSuccessType "!llvm.ptr" (LLVM.PointerType.mk)

/-! ## LLVM Void type -/
#assert expectSuccessType "!llvm.void" (LLVM.VoidType.mk)

/-! ## LLVM Array type -/
#assert expectSuccessType "!llvm.array<2 x i32>" (LLVM.ArrayType.mk 2 $ IntegerType.mk 32)
#assert expectSuccessAttr "!llvm.array<2 x !llvm.array<3x i64>>" (LLVM.ArrayType.mk 2 $ LLVM.ArrayType.mk 3 $ IntegerType.mk 64)

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

/-! ## CUDA Pointer type -/
#assert expectSuccessType "!cuda_tile.ptr<i1>" (CudaTile.PointerType.mk (IntegerType.mk 1))
#assert expectSuccessType "!cuda_tile.ptr<i32>" (CudaTile.PointerType.mk (IntegerType.mk 32))
#assert expectErrorType "!cuda_tile.ptr<16>" "integer type expected" (some 15)
-- A `!cuda_tile.ptr<...>` may appear as a (parenthesized) function-type input. See #675.
#assert expectSuccessType "(!cuda_tile.ptr<i1>) -> ()"
  (FunctionType.mk #[(CudaTile.PointerType.mk (IntegerType.mk 1) : Attribute)] #[] (isVarArg := false))

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
