// RUN: veir-opt %s -p="felt-combine" | filecheck %s
//
// Constant-fold sub, mul, neg.
// Soundness: constant_fold_sub, constant_fold_mul, constant_fold_neg.

"builtin.module"() ({
  %a = "felt.const"() <{"value" = #felt<const 7> : !felt.type}> : () -> !felt.type
  %b = "felt.const"() <{"value" = #felt<const 3> : !felt.type}> : () -> !felt.type
  %d = "felt.sub"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
  %p = "felt.mul"(%a, %b) : (!felt.type, !felt.type) -> !felt.type
  %n = "felt.neg"(%a) : (!felt.type) -> !felt.type
}) : () -> ()

// Each constant op gets folded to its computed value.
//
// CHECK:        "builtin.module"() ({
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 4> : !felt.type}> : () -> !felt.type
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 21> : !felt.type}> : () -> !felt.type
// CHECK-DAG:      %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const -7> : !felt.type}> : () -> !felt.type
// CHECK-NOT:      "felt.sub"
// CHECK-NOT:      "felt.mul"
// CHECK-NOT:      "felt.neg"
// CHECK:        }) : () -> ()
