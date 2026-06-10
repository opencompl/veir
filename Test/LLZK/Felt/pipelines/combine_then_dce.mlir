// RUN: veir-opt %s -p="felt-combine,dce" | filecheck %s
//
// Composed pipeline: felt-combine collapses arithmetic, then dce removes
// the now-unused constant/add intermediates. Anchored by a `constrain.eq`
// so DCE keeps the value chain it consumes (constrain.eq has 0 results
// and is treated as side-effecting by `Veir/Passes/DCE/dce.lean`'s
// `hasSideEffects` heuristic).
//
// Input: a + 0 should fold to a; registered-field 1 + 2 should fold to 3;
// the constrain then sees `constrain.eq(a, const 3)`. With `felt-combine`
// alone the dead `const 0`, `const 1`, `const 2` survive; with dce chained
// they disappear. The bare-field no-fold case is covered by the Phase 8
// companion `unspecified_add_fold.llzk` target.

"builtin.module"() ({
^bb0(%a: !felt.type<"babybear">):
  %z = "felt.const"() <{value = #felt<const 0> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %s = "felt.add"(%a, %z) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %c1 = "felt.const"() <{value = #felt<const 1> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %c2 = "felt.const"() <{value = #felt<const 2> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %three = "felt.add"(%c1, %c2) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  "constrain.eq"(%s, %three) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
}) : () -> ()

// Only the synthesized const 3 and the constrain survive.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 3> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    "felt.add"
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 0>
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 1>
// CHECK-NOT:    "felt.const"() <{"value" = #felt<const 2>
