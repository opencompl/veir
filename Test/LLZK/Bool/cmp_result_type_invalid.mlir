// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.cmp: Expected result 0 to have i1 type
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %0 = "bool.cmp"(%a, %b) <{predicate = #bool<cmp eq>}> : (!felt.type, !felt.type) -> i32
}) : () -> ()
