// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace
// RUN: MLIR_INVALID

"builtin.module"() ({
  ^bb0:
    "test.test"()[^bb1] : () -> ()
}) : () -> ()

// CHECK:block-not-defined.mlir:6:19: error: block %bb1 was used but never defined
// CHECK-NEXT:    "test.test"()[^bb1] : () -> ()
// CHECK-NEXT:                  ^
