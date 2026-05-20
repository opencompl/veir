// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Tier 2 telescoping rewrites:
//   (x + c) - c -> x    (add_sub_const_cancel)
//   (x - c) + c -> x    (sub_add_const_cancel)

"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type):
  %c5 = "felt.const"() <{"value" = #felt<const 5> : !felt.type}> : () -> !felt.type
  // (a + 5) - 5 -> a
  %a_plus  = "felt.add"(%a, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t1      = "felt.sub"(%a_plus, %c5) : (!felt.type, !felt.type) -> !felt.type
  // (b - 5) + 5 -> b
  %b_minus = "felt.sub"(%b, %c5) : (!felt.type, !felt.type) -> !felt.type
  %t2      = "felt.add"(%b_minus, %c5) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()

// Both telescoped pairs vanish; the inner add/sub stay because their
// results are no longer used by the rewritten outer op but DCE doesn't
// remove them.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 5> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %{{[^ ]+}} = "felt.add"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:     %{{[^ ]+}} = "felt.sub"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:   }) : () -> ()
