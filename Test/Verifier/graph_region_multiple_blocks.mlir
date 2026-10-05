// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
^bb0:
^bb1:
}) : () -> ()

// CHECK: Graph regions may contain at most one block
