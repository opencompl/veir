// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
  %r = "arith.constant"() : () -> i32
}) : () -> ()

// CHECK:missing-properties.mlir:5:27: error: arith.constant: missing 'value' property
// CHECK-NEXT:  %r = "arith.constant"() : () -> i32
// CHECK-NEXT:                          ^
