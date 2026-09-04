// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: cast.tofelt: Expected operand to have i1 or index type
"builtin.module"() ({
^bb0(%arg: !felt.type):
  %0 = "cast.tofelt"(%arg) : (!felt.type) -> !felt.type
}) : () -> ()
