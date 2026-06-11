// RUN: not veir-opt %s 2>&1 | filecheck %s

// Negative test: bool.cmp with predicate out of the 0..5 range.
// The typed properties dispatch rejects this; without the typed path
// (i.e. unregistered fallthrough) no such check would fire.

// CHECK: 'predicate' must be in 0..5
"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %x = "bool.cmp"(%a, %b) <{predicate = 42 : i32}> : (!felt.type, !felt.type) -> i1
}) : () -> ()
