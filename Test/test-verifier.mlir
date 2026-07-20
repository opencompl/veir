// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: veir-opt --disable-verifiers %s 2>&1 | filecheck --check-prefix=CHECK-NO-VERIFY %s

"builtin.module"() ({

}, {}) : () -> ()

// CHECK: Error verifying input program: Expected 1 region
// CHECK-NO-VERIFY: "builtin.module"() ({}, {}) : () -> ()
