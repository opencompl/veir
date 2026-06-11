// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: cast.tofelt with no operand triggers the typed
// "Expected 1 operand" arm; the unregistered fallthrough would accept.

// CHECK: Error verifying input program: Expected 1 operand
"builtin.module"() ({
^bb0():
  %0 = "cast.tofelt"() : () -> !felt.type
}) : () -> ()
