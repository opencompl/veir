// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: cast.toindex: Expected operand to have FeltType
"builtin.module"() ({
^bb0(%value: index):
  %0 = "cast.toindex"(%value) : (index) -> index
}) : () -> ()
