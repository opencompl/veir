// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The companion to Test/Parsing/integer-attr-out-of-range-*.mlir for
// `arith.constant`: an `IntegerAttr` of width N only admits [-2^(N-1), 2^N), so
// `256 : i8` names a value the attribute type cannot represent, and both
// mlir-opt and veir-opt reject it.
//
// The exact wording of the diagnostic is not important; that the input is
// rejected is.

"builtin.module"() ({
  "func.func"() <{sym_name = "f", function_type = () -> i8}> ({
    %0 = "arith.constant"() <{value = 256 : i8}> : () -> i8
    "func.return"(%0) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
