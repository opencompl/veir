// RUN: veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: Expected 1 region
"builtin.module"() ({

}, {}) : () -> ()