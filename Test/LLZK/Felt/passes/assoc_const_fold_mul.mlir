// RUN: veir-opt %s -p="felt-combine,canonicalize" | filecheck %s
// felt.mul (felt.mul x c1) c2 -> felt.mul x (c1 * c2).

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "assoc_const_fold_mul", function_type = (!felt.type<"babybear">, !felt.type<"babybear">) -> ()}> ({
^bb0(%x: !felt.type<"babybear">, %anchor: !felt.type<"babybear">):
  // CHECK-NOT:    #felt<const 3>
  %c3 = "felt.const"() <{"value" = #felt<const 3 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-NOT:    #felt<const 4>
  %c4 = "felt.const"() <{"value" = #felt<const 4 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %inner = "felt.mul"(%x, %c3) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // CHECK:          %[[C12:[^ ]+]] = "felt.const"() <{"value" = #felt<const 12 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  // CHECK-NEXT:     %[[P:[^ ]+]] = "felt.mul"(%{{[^,]+}}, %[[C12]]) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %outer = "felt.mul"(%inner, %c4) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // CHECK-NEXT:     "constrain.eq"(%[[P]], %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%outer, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
