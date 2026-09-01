// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID
// Expected to fail until `llvm.mlir.constant` handles the value attribute's
// integer width the way MLIR does; drop the XFAIL with the fix.
// XFAIL: *

// An MLIR `IntegerAttr` of width N is an APInt of width N, so the literal must
// fit: mlir-opt accepts only [-2^(N-1), 2^N) and rejects everything else with
// "integer constant out of range for attribute".  Veir stores the literal as an
// unbounded `Int` and accepts it, which lets IR name a value the attribute type
// cannot represent at all.
//
//   mlir-opt: error: integer constant out of range for attribute
//   veir-opt: accepted; `-129 : i8` survives into the interpreter
//
// The exact wording of the diagnostic is not important; that the input is
// rejected is.

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i8 ()>, linkage = #llvm.linkage<external>, sym_name = "f", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = -129 : i8}> : () -> i8
    "llvm.return"(%0) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute

// There is no reference lowering for this file: upstream MLIR never gets past
// parsing it.
//
//   mlir-opt --convert-to-llvm Test/Parsing/integer-attr-out-of-range-negative-overflow.mlir
//
//   error: integer constant out of range for attribute
//     %0 = "llvm.mlir.constant"() <{value = -129 : i8}> : () -> i8
