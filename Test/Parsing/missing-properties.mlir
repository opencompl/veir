// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %r = "arith.constant"() : () -> i32
}) : () -> ()

// CHECK:missing-properties.mlir:4:27: error: arith.constant: missing 'value' property
// CHECK-NEXT:  %r = "arith.constant"() : () -> i32
// CHECK-NEXT:                          ^
