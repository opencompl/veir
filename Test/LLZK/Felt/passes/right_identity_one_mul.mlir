// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// felt.mul x (felt.const 1) -> x.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "right_identity_one_mul", function_type = (!felt.type, !felt.type) -> ()}> ({
^bb0(%a: !felt.type, %anchor: !felt.type):
  // CHECK-NOT:    #felt<const 1>
  %one = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
  %r = "felt.mul"(%a, %one) : (!felt.type, !felt.type) -> !felt.type
  // Non-matching: rhs is const 2, must stay.
  // CHECK:          %[[TWO:[^ ]+]] = "felt.const"() <{"value" = #felt<const 2>}> : () -> !felt.type
  %two = "felt.const"() <{"value" = #felt<const 2> : !felt.type}> : () -> !felt.type
  // CHECK-NEXT:     %[[S:[^ ]+]] = "felt.mul"(%{{[^,]+}}, %[[TWO]]) : (!felt.type, !felt.type) -> !felt.type
  %s = "felt.mul"(%a, %two) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%r, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "constrain.eq"(%[[S]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
