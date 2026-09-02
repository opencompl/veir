// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// felt.add x (felt.const 0) -> x.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "right_identity", function_type = (!felt.type, !felt.type) -> ()}> ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  // CHECK-NOT:    "felt.const"() <{"value" = #felt<const 0>
  %z = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
  %r = "felt.add"(%a, %z) : (!felt.type, !felt.type) -> !felt.type
  // Sanity: a non-matching add (rhs is not zero) is left untouched.
  // CHECK:          %[[C1:[^ ]+]] = "felt.const"() <{"value" = #felt<const 1>}> : () -> !felt.type
  %c1 = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
  // CHECK-NEXT:     %[[S:[^ ]+]] = "felt.add"(%{{[^,]+}}, %[[C1]]) : (!felt.type, !felt.type) -> !felt.type
  %s = "felt.add"(%a, %c1) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "constrain.eq"(%[[S]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
