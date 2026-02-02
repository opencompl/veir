// RUN: veir-opt %s | filecheck %s

"builtin.module"() ({}) : () -> ()

// CHECK: "builtin.module"() ({}) : () -> ()