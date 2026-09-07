// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that a numeric attribute with a non-integer/float-type suffix is rejected.

"builtin.module"() ({
  %a = "test.test"() <{"value" = 0 : 2}> : () -> i32
}) : () -> ()

// CHECK:invalid-integer-attr.mlir:6:38: error: integer or float type expected after ':' in numeric attribute
// CHECK-NEXT:  %a = "test.test"() <{"value" = 0 : 2}> : () -> i32
// CHECK-NEXT:                                     ^
