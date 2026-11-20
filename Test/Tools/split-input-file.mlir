// RUN: not veir-opt --split-input-file %s | filecheck %s
// RUN: not veir-opt --split-input-file= %s | filecheck %s
// RUN: not veir-opt --split-input-file %s 2>&1 >/dev/null | filecheck %s --check-prefix=ERR

"builtin.module"() ({}) : () -> ()
// CHECK: "builtin.module"() ({}) : () -> ()

// -----

// A failing chunk does not stop the following ones.
"builtin.module"() ({}) : () -> i32
// ERR: split-input-file.mlir:[[# @LINE - 1]]:1: error: operation 'builtin.module' declares 1 result
// CHECK-NEXT: // {{-----}}

// The marker also splits the input in the middle of a line.
// ----- "builtin.module"() ({}) : () -> ()
// CHECK-NEXT: // {{-----}}
// CHECK-NEXT: "builtin.module"() ({}) : () -> ()
// CHECK-NOT: {{.}}
