// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

this is not an operation

// CHECK:operation-expected.mlir:4:1: error: operation expected
// CHECK-NEXT:this is not an operation
// CHECK-NEXT:^
