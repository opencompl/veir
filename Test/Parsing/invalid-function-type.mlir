// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that a function type with a trailing comma in its inputs is rejected.

"builtin.module"() ({
  %a = "test.test"() : () -> ((i32, ) -> i32)
}) : () -> ()

// CHECK:invalid-function-type.mlir:6:37: error: type expected
// CHECK-NEXT:  %a = "test.test"() : () -> ((i32, ) -> i32)
// CHECK-NEXT:                                    ^
