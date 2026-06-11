// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

this is not an operation

// CHECK:operation-expected.mlir:3:1: error: operation expected
// CHECK-NEXT:this is not an operation
// CHECK-NEXT:^
