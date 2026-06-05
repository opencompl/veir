// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %a = "test.test"() : (i32) -> i32
}) : () -> ()

// CHECK:operand-count-mismatch.mlir:4:8: error: operation 'test.test' declares 1 operand types, but 0 operands were provided
// CHECK-NEXT:  %a = "test.test"() : (i32) -> i32
// CHECK-NEXT:       ^
