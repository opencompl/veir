// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that an integer attribute with a non-integer-type suffix is rejected.

"builtin.module"() ({
  %a = "test.test"() <{"value" = 0 : 2}> : () -> i32
}) : () -> ()

// CHECK:invalid-integer-attr.mlir:6:38: error: integer type expected after ':' in integer attribute
// CHECK-NEXT:  %a = "test.test"() <{"value" = 0 : 2}> : () -> i32
// CHECK-NEXT:                                     ^
