// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
  ^bb0:
    "test.test"() : () -> ()
  ^bb0:
    "test.test"() : () -> ()
}) : () -> ()

// CHECK:block-already-defined.mlir:7:3: error: block %bb0 has already been defined
// CHECK-NEXT:  ^bb0:
// CHECK-NEXT:  ^
// CHECK-NEXT:block-already-defined.mlir:5:3: note: block previously defined here
// CHECK-NEXT:  ^bb0:
// CHECK-NEXT:  ^
