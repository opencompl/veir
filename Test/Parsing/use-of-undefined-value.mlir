// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
  %b = "test.test"(%c) : (i32) -> i1
}) : () -> ()

// CHECK:use-of-undefined-value.mlir:5:20: error: use of undefined value %c
// CHECK-NEXT:  %b = "test.test"(%c) : (i32) -> i1
// CHECK-NEXT:                   ^
