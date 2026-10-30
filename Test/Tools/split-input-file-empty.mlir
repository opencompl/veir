// RUN: not veir-opt --split-input-file %s 2>&1 | filecheck %s

// Unlike mlir-opt, veir-opt inserts no implicit module, so an empty chunk fails.
// CHECK: split-input-file-empty.mlir:[[# @LINE + 4]]:1: error: operation expected

"builtin.module"() ({}) : () -> ()
// -----
// -----
"builtin.module"() ({}) : () -> ()
