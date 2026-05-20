// RUN: veir-opt %s -p="felt-combine,dce" | filecheck %s
//
// Tier 2 telescoping + DCE composition: `(a + 5) - 5` should collapse
// to `a`, and the now-dead `add` and `const 5` should disappear.
// Anchored by `constrain.eq(a, b)` so DCE keeps the value chain that
// produced %a-equivalent.

"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %c5      = "felt.const"() <{value = #felt<const 5> : !felt.type}> : () -> !felt.type
  %a_plus  = "felt.add"(%a, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t1      = "felt.sub"(%a_plus, %c5) : (!felt.type, !felt.type) -> !felt.type
  "constrain.eq"(%t1, %b) : (!felt.type, !felt.type) -> ()
}) : () -> ()

// Telescoping collapses %t1 to %a; then DCE removes the now-dead
// add and the const 5. Only the constrain survives.
//
// CHECK:        "builtin.module"() ({
// CHECK:          "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:   }) : () -> ()
// CHECK-NOT:    "felt.add"
// CHECK-NOT:    "felt.sub"
// CHECK-NOT:    "felt.const"
