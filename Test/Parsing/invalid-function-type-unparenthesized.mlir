// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

// A function type's input must be a parenthesized type list, matching MLIR: the
// unparenthesized form `i32 -> ()` is rejected (use `(i32) -> ()` instead). See #675.

"builtin.module"() ({
  "func.func"() <{function_type = i32 -> (), sym_name = "main"}> ({
    ^bb0(%arg0: i32):
      "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:invalid-function-type-unparenthesized.mlir:8:39: error: closing delimiter '}' expected
// CHECK-NEXT:  "func.func"() <{function_type = i32 -> (), sym_name = "main"}> ({
// CHECK-NEXT:                                      ^
