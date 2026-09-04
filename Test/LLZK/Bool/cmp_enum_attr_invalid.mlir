// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: #bool<...> expects `cmp` before the predicate
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %x = "bool.cmp"(%a, %b) <{predicate = #bool<eq>}> : (!felt.type, !felt.type) -> i1
}) : () -> ()
