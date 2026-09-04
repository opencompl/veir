// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: cast.tofelt: Expected result to have FeltType
"builtin.module"() ({
^bb0(%value: index):
  %0 = "cast.tofelt"(%value) : (index) -> index
}) : () -> ()
