// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

// The negative-zero restriction also applies to hexadecimal literals.
"builtin.module"() ({
  "test.op"() {a = -0x0 : i64} : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
