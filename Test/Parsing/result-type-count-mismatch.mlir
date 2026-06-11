// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a:2 = "test.test"() : () -> i32
}) : () -> ()

// CHECK:result-type-count-mismatch.mlir:4:10: error: operation 'test.test' declares 1 result types, but 2 result values were provided
// CHECK-NEXT:  %a:2 = "test.test"() : () -> i32
// CHECK-NEXT:         ^
