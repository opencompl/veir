// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.store: Expected address operand to have index type
"builtin.module"() ({
^bb0(%addr: i32, %val: !felt.type):
  "ram.store"(%addr, %val) : (i32, !felt.type) -> ()
}) : () -> ()
