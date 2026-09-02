// RUN: veir-opt %s -p="felt-combine" | filecheck %s
// felt.sub x x -> felt.const 0, matching operands by SSA identity.

// CHECK:        "builtin.module"() ({
"builtin.module"() ({
  "function.def"() <{sym_name = "self_subtraction", function_type = (!felt.type, !felt.type, !felt.type) -> ()}> ({
^bb0(%x: !felt.type, %y: !felt.type, %anchor: !felt.type):
  // Same value on both sides — folds to felt.const 0.
  // CHECK:          %[[Z:[^ ]+]] = "felt.const"() <{"value" = #felt<const 0>}> : () -> !felt.type
  %s1 = "felt.sub"(%x, %x) : (!felt.type, !felt.type) -> !felt.type
  // Two distinct block-args, even if semantically equal at runtime —
  // doesn't match (lhs ≠ rhs as ValuePtrs). Op survives.
  // CHECK-NEXT:     %[[S2:[^ ]+]] = "felt.sub"(%{{[^,]+}}, %{{[^)]+}}) : (!felt.type, !felt.type) -> !felt.type
  %s2 = "felt.sub"(%x, %y) : (!felt.type, !felt.type) -> !felt.type
  // CHECK-NEXT:     "constrain.eq"(%[[Z]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s1, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "constrain.eq"(%[[S2]], %{{[^)]+}}) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%s2, %anchor) : (!felt.type, !felt.type) -> ()
  // CHECK-NEXT:     "function.return"() : () -> ()
  "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
