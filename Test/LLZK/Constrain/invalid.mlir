// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: constrain.eq with a result triggers the typed
// "Expected 0 results" arm. (The op is a constraint emission with no
// SSA value.)

// CHECK: Error verifying input program: Expected 0 results
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "constrain.eq"(%a, %b) : (!felt.type, !felt.type) -> i32
}) : () -> ()
