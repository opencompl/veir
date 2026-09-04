// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: error: bool.and: expected no properties, but got 1 property
"builtin.module"() ({
^bb0(%a: i1, %b: i1):
  %0 = "bool.and"(%a, %b) <{unexpected = 1 : i32}> : (i1, i1) -> i1
}) : () -> ()
