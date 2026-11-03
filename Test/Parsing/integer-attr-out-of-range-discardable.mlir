// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// The range check applies to every integer attribute, including a discardable
// one on an operation that never looks at it.

"builtin.module"() ({
  "test.op"() {a = 256 : i8} : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
