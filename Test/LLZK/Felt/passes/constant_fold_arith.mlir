// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Constant-fold registered-field sub, mul, neg.
// Soundness: constant_fold_sub, constant_fold_mul, constant_fold_neg.

"builtin.module"() ({
  %a = "felt.const"() <{"value" = #felt<const 7> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %b = "felt.const"() <{"value" = #felt<const 3> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %d = "felt.sub"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %p = "felt.mul"(%a, %b) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %n = "felt.neg"(%a) : (!felt.type<"babybear">) -> !felt.type<"babybear">
}) : () -> ()

// Each constant op gets folded to its computed value.
//
// CHECK:        "builtin.module"() ({
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 4> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 21> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 2013265914> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
// CHECK-NOT:      "felt.sub"
// CHECK-NOT:      "felt.mul"
// CHECK-NOT:      "felt.neg"
// CHECK:        }) : () -> ()
