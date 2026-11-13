// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: trailing-input.mlir:[[# @LINE + 3]]:1: error: unexpected trailing input after top-level operation

"builtin.module"() ({}) : () -> ()
"builtin.module"() ({}) : () -> ()
