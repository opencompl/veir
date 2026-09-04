// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.store: Expected value operand to have FeltType
"builtin.module"() ({
^bb0(%address: index, %value: i1):
  "ram.store"(%address, %value) : (index, i1) -> ()
}) : () -> ()
