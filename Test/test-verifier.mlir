// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: Expected 1 region
"builtin.module"() ({

}, {}) : () -> ()

// RUN: veir-opt --disable-verifiers %s 2>&1 | filecheck --check-prefix=CHECK-NO-VERIFY %s

// CHECK-NO-VERIFY: "builtin.module"() ({}, {}) : () -> ()
