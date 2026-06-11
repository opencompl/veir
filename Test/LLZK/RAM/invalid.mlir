// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: ram.store with a result. The typed verifier arm
// expects 0 results; the unregistered fallthrough would not error.
// Seeing this exact message confirms the .ram .store path is reached.

// CHECK: Error verifying input program: Expected 0 results
"builtin.module"() ({
^bb0(%addr: index, %val: !felt.type):
  %0 = "ram.store"(%addr, %val) : (index, !felt.type) -> i32
}) : () -> ()
