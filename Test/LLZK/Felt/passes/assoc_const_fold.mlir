// RUN: veir-opt %s -p="felt-combine,canonicalize" | filecheck %s
// felt.add (felt.add x c1) c2 -> felt.add x (c1 + c2).

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "assoc_const_fold", function_type = (!felt.type<"babybear">, !felt.type<"babybear">) -> ()}> ({
^bb0(%x: !felt.type<"babybear">, %anchor: !felt.type<"babybear">):
  // ((x + 10) + 32) ->[assoc] (x + 42)
  // CHECK-NOT:    #felt<const 10>
  %c10 = "felt.const"() <{"value" = #felt<const 10 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  %inner = "felt.add"(%x, %c10) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // CHECK-NOT:    #felt<const 32>
  %c32 = "felt.const"() <{"value" = #felt<const 32 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK:          %[[C42:[^ ]+]] = "felt.const"() <{"value" = #felt<const 42 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  // CHECK-NEXT:     %[[SUM:[^ ]+]] = "felt.add"(%{{[^,]+}}, %[[C42]]) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  %outer = "felt.add"(%inner, %c32) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // CHECK-NEXT:     "constrain.eq"(%[[SUM]], %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%outer, %anchor) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
