// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
  ^bb0:
    "test.test"() : () -> ()
  ^bb0:
    "test.test"() : () -> ()
}) : () -> ()

// CHECK:block-already-defined.mlir:6:3: error: block %bb0 has already been defined
// CHECK-NEXT:  ^bb0:
// CHECK-NEXT:  ^
// CHECK-NEXT:block-already-defined.mlir:4:3: note: block previously defined here
// CHECK-NEXT:  ^bb0:
// CHECK-NEXT:  ^
