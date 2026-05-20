// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.neg (felt.neg x) -> x.  Soundness: neg_neg_to_self.

"builtin.module"() ({
^bb0(%a: !felt.type):
  %n1 = "felt.neg"(%a) : (!felt.type) -> !felt.type
  %n2 = "felt.neg"(%n1) : (!felt.type) -> !felt.type
}) : () -> ()

// The outer neg disappears; the inner neg's result is the block arg,
// but the inner op itself stays (no DCE).
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.neg"(%{{[^)]+}}) : (!felt.type) -> !felt.type
// CHECK-NOT:      "felt.neg"
// CHECK:        }) : () -> ()
