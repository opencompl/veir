// RUN: veir-opt %s -p="canonicalize,felt-combine,dce" | filecheck %s
// Canonicalize and felt-combine simplify the values before DCE removes dead ops.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "combine_then_dce", function_type = (!felt.type<"babybear">) -> ()}> ({
^bb0(%a: !felt.type<"babybear">):
  // CHECK-NOT:    "felt.const"() <{"value" = #felt<const 0>
  %z = "felt.const"() <{value = #felt<const 0 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-NOT:    "felt.add"
  %s = "felt.add"(%a, %z) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // CHECK-NOT:    "felt.const"() <{"value" = #felt<const 1>
  %c1 = "felt.const"() <{value = #felt<const 1 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK-NOT:    "felt.const"() <{"value" = #felt<const 2>
  %c2 = "felt.const"() <{value = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
  // CHECK:          %{{[^ ]+}} = "felt.const"() <{"value" = #felt<const 3 : !felt.type<"babybear">>}> : () -> !felt.type<"babybear">
  %three = "felt.add"(%c1, %c2) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
  // CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  "constrain.eq"(%s, %three) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
