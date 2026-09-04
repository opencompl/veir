// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.load: Expected address operand to have index type
"builtin.module"() ({
^bb0(%address: i32):
  %0 = "ram.load"(%address) : (i32) -> !felt.type
}) : () -> ()
