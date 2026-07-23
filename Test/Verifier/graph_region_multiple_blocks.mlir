// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
^bb0:
^bb1:
}) : () -> ()

// CHECK: Graph regions may contain at most one block
