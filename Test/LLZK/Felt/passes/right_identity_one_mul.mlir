// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul x (felt.const 1) -> x.  Soundness: right_identity_one_mul.

"builtin.module"() ({
^bb0(%a: !felt.type):
  %one = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
  %r = "felt.mul"(%a, %one) : (!felt.type, !felt.type) -> !felt.type
  // Non-matching: rhs is const 2, must stay.
  %two = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
  %s = "felt.mul"(%a, %two) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()

// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %{{[^ ]+}} = "felt.mul"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NEXT:   }) : () -> ()
