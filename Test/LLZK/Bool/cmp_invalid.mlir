// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: bool.cmp: expected 'predicate' to be a #bool<cmp ...> attribute, got 42 : i32
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %x = "bool.cmp"(%a, %b) <{predicate = 42 : i32}> : (!felt.type, !felt.type) -> i1
}) : () -> ()
