// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.add x (felt.neg x) -> felt.const 0.  Soundness: add_neg_to_zero.

"builtin.module"() ({
^bb0(%a: !felt.type):
  %na = "felt.neg"(%a) : (!felt.type) -> !felt.type
  %r = "felt.add"(%a, %na) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()

// The add collapses to a const 0; the neg stays (its result is no
// longer used but DCE doesn't run here).
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.neg"(%{{[^)]+}}) : (!felt.type) -> !felt.type
// CHECK-NEXT:     %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NOT:      "felt.add"
// CHECK:        }) : () -> ()
