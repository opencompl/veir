// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// felt.add x (felt.neg x) -> felt.const 0.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "add_neg_to_zero", function_type = (!felt.type, !felt.type) -> ()}> ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  // CHECK-NOT:    "felt.neg"
  %na = "felt.neg"(%a) : (!felt.type) -> !felt.type
  // CHECK-NOT:    "felt.add"
  // CHECK:          %[[Z:[^ ]+]] = "felt.const"() <{"value" = #felt<const 0>}> : () -> !felt.type
  %r = "felt.add"(%a, %na) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"(%[[Z]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
