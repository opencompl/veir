// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: cast.tofelt: Expected 1 operand(s)
"builtin.module"() ({
^bb0():
  %0 = "cast.tofelt"() : () -> !felt.type
}) : () -> ()
