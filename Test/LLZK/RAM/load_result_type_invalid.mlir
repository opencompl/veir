// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.load: Expected result to have FeltType
"builtin.module"() ({
^bb0(%address: index):
  %0 = "ram.load"(%address) : (index) -> i1
}) : () -> ()
