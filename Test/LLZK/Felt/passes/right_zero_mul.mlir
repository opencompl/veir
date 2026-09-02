// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// felt.mul x (felt.const 0) -> felt.const 0.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "right_zero_mul", function_type = (!felt.type, !felt.type) -> ()}> ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  // CHECK:          %[[Z:[^ ]+]] = "felt.const"() <{"value" = #felt<const 0>}> : () -> !felt.type
  // CHECK-NOT:    "felt.mul"
  %r = "felt.mul"(%a, %z) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"(%[[Z]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
