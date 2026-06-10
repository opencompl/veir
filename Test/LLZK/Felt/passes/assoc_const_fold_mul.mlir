// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// felt.mul (felt.mul x c1) c2 -> felt.mul x (c1*c2).
// Soundness: assoc_const_fold_mul.

"builtin.module"() ({
^bb0(%x: !felt.type<"babybear">):
  %c3 = "felt.const"() <{"value" = #felt<const 3> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %c4 = "felt.const"() <{"value" = #felt<const 4> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %inner = "felt.mul"(%x, %c3) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %outer = "felt.mul"(%inner, %c4) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
}) : () -> ()

// After folding, a single mul x (const 12) remains. The original two
// constants and the inner mul are no longer used but stay (no DCE).
//
// CHECK:        "builtin.module"() ({
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 12> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK:          %{{[^ ]+}} = "felt.mul"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
// CHECK-NOT:      "felt.mul"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
// CHECK:        }) : () -> ()
