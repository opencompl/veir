// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.and: Expected result 0 to have i1 type
"builtin.module"() ({
^bb0(%a: i1, %b: i1):
  %0 = "bool.and"(%a, %b) : (i1, i1) -> i32
}) : () -> ()
