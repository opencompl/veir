// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: felt.add with 1 operand instead of 2 triggers the typed
// "Expected 2 operands" arm. Confirms the .felt .add typed verifier
// path is reached. (Felt landed before invalid.mlir was a standard;
// this test was added during the Tier-1 review pass for consistency.)

// CHECK: Error verifying input program: Expected 2 operands
"builtin.module"() ({
^bb0(%a: !felt.type):
  %0 = "felt.add"(%a) : (!felt.type) -> !felt.type
}) : () -> ()
