// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: cast.toindex: Expected result to have index type
"builtin.module"() ({
^bb0(%value: !felt.type):
  %0 = "cast.toindex"(%value) : (!felt.type) -> i1
}) : () -> ()
