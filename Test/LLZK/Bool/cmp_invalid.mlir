// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: 'predicate' must be in 0..5
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %x = "bool.cmp"(%a, %b) <{predicate = 42 : i32}> : (!felt.type, !felt.type) -> i1
}) : () -> ()
