// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// Like MLIR, reject a minus sign on an integer zero.
"builtin.module"() ({
  "test.op"() {a = -0 : i8} : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
