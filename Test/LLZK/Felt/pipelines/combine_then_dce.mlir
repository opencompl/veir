// RUN: veir-opt %s -p="felt-combine,dce" | filecheck %s
//
// Composed pipeline: felt-combine collapses arithmetic, then dce removes
// the now-unused constant/add intermediates. Anchored by a `constrain.eq`
// so DCE keeps the value chain it consumes (constrain.eq has 0 results
// and is treated as side-effecting by `Veir/Passes/DCE/dce.lean`'s
// `hasSideEffects` heuristic).
//
// Input: a + 0 should fold to a; 1 + 2 should fold to 3; the constrain
// then sees `constrain.eq(a, const 3)`. With `felt-combine` alone the
// dead `const 0`, `const 1`, `const 2` survive; with dce chained they
// disappear.

"builtin.module"() ({
^bb0(%a: !felt.type):
  %z = "felt.const"() <{value = #felt<const 0> : !felt.type}> : () -> !felt.type
  %s = "felt.add"(%a, %z) : (!felt.type, !felt.type) -> !felt.type
  %c1 = "felt.const"() <{value = #felt<const 1> : !felt.type}> : () -> !felt.type
  %c2 = "felt.const"() <{value = #felt<const 2> : !felt.type}> : () -> !felt.type
  %three = "felt.add"(%c1, %c2) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%s, %three) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// Only the synthesized const 3 and the constrain survive.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 3> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    "felt.add"
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 0>
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 1>
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 2>
