// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The top-level operation is detached. Its result is resolved through a
// forward reference from inside the nested module, but therefore has no parent
// region and cannot be used within the module's isolated scope.

%root = "test.test"() ({
  "builtin.module"() ({
    "test.test"(%root) : (i32) -> ()
  }) : () -> ()
}) : () -> i32

// CHECK: test.test: operand is unlinked from any region
