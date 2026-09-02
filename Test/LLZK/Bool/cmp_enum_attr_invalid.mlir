// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: #bool<...> expects one of eq, ne, lt, le, gt, ge
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %x = "bool.cmp"(%a, %b) <{predicate = #bool<cmp bogus>}> : (!felt.type, !felt.type) -> i1
}) : () -> ()
