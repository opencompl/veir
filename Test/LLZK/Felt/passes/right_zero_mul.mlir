// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul x (felt.const 0) -> felt.const 0.  Soundness: right_zero_mul.

"builtin.module"() ({
^bb0(%a: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  %r = "felt.mul"(%a, %z) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()

// The mul collapses to a const 0; the block-arg %a and the original
// zero const are both unused after rewrite but DCE doesn't run.
//
// CHECK:        "builtin.module"() ({
// CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NEXT:     %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
// CHECK-NOT:      "felt.mul"
// CHECK:        }) : () -> ()
