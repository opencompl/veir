// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: bool.cmp: Expected operands to have FeltType
"builtin.module"() ({
^bb0(%a: i1, %b: i1):
  %0 = "bool.cmp"(%a, %b) <{predicate = #bool<cmp eq>}> : (i1, i1) -> i1
}) : () -> ()
