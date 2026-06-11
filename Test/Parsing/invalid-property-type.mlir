// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  %r = "arith.constant"() <{"value" = "hello"}> : () -> i32
}) : () -> ()

// CHECK:invalid-property-type.mlir:4:27: error: arith.constant: expected 'value' to be an integer attribute, but got "hello"
// CHECK-NEXT:  %r = "arith.constant"() <{"value" = "hello"}> : () -> i32
// CHECK-NEXT:                          ^
