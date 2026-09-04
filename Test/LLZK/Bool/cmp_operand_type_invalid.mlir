// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.cmp: Expected operands to have the same type
"builtin.module"() ({
^bb0(%a: !felt.type<"babybear">, %b: !felt.type<"bn254">):
  %0 = "bool.cmp"(%a, %b) <{predicate = #bool<cmp eq>}> : (!felt.type<"babybear">, !felt.type<"bn254">) -> i1
}) : () -> ()
