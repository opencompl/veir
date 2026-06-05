// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  "test.test"() : () ->
}) : () -> ()

// CHECK:type-expected.mlir:5:1: error: type expected
// CHECK-NEXT:}) : () -> ()
// CHECK-NEXT:^
