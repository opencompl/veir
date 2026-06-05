// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %b = "test.test"(%c) : (i32) -> i1
}) : () -> ()

// CHECK:use-of-undefined-value.mlir:4:20: error: use of undefined value %c
// CHECK-NEXT:  %b = "test.test"(%c) : (i32) -> i1
// CHECK-NEXT:                   ^
