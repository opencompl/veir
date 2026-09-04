// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.and: Expected operand 0 to have i1 type
"builtin.module"() ({
^bb0(%a: i32, %b: i32):
  %0 = "bool.and"(%a, %b) : (i32, i32) -> i1
}) : () -> ()
