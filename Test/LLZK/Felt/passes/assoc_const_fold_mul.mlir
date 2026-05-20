// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul (felt.mul x c1) c2 -> felt.mul x (c1*c2).
// Soundness: assoc_const_fold_mul.

"builtin.module"() ({
^bb0(%x: !felt.type):
  %c3 = "felt.const"() <{"value" = #felt<const 3> : !felt.type}> : () -> !felt.type
  %c4 = "felt.const"() <{"value" = #felt<const 4> : !felt.type}> : () -> !felt.type
  %inner = "felt.mul"(%x, %c3) : (!felt.type, !felt.type) -> !felt.type
  %outer = "felt.mul"(%inner, %c4) : (!felt.type, !felt.type) -> !felt.type
}) : () -> ()

// After folding, a single mul x (const 12) remains. The original two
// constants and the inner mul are no longer used but stay (no DCE).
//
// CHECK:        "builtin.module"() ({
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 12> : !felt.type}> : () -> !felt.type
// CHECK:          %{{[^ ]+}} = "felt.mul"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK-NOT:      "felt.mul"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
// CHECK:        }) : () -> ()
