// RUN: VEIR_ROUNDTRIP

// Circomlib IsZero constraint system, adapted from
// llzk-lib/test/Conversions/llzk_to_smt_no_cf_iszero.llzk:
//   out = -in * inv + 1
//   in * out = 0

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "iszero", function_type = (!felt.type, !felt.type, !felt.type) -> ()}> ({
  // CHECK:         ^{{.*}}(%[[IN:[0-9a-zA-Z_]+]] : !felt.type, %[[OUT:[0-9a-zA-Z_]+]] : !felt.type, %[[INV:[0-9a-zA-Z_]+]] : !felt.type):
  ^bb0(%in: !felt.type, %out: !felt.type, %inv: !felt.type):
    // CHECK-NEXT:      %[[NEG:[0-9a-zA-Z_]+]] = "felt.neg"(%[[IN]])
    %0 = "felt.neg"(%in) : (!felt.type) -> !felt.type
    // CHECK-NEXT:      %[[PROD:[0-9a-zA-Z_]+]] = "felt.mul"(%[[NEG]], %[[INV]])
    %1 = "felt.mul"(%0, %inv) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NEXT:      %[[ONE:[0-9a-zA-Z_]+]] = "felt.const"() <{"value" = #felt<const 1>}>
    %c1 = "felt.const"() <{"value" = #felt<const 1> : !felt.type}> : () -> !felt.type
    // CHECK-NEXT:      %[[SUM:[0-9a-zA-Z_]+]] = "felt.add"(%[[PROD]], %[[ONE]])
    %2 = "felt.add"(%1, %c1) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NEXT:      "constrain.eq"(%[[OUT]], %[[SUM]])
    "constrain.eq"(%out, %2) : (!felt.type, !felt.type) -> ()
    // CHECK-NEXT:      %[[ZPROD:[0-9a-zA-Z_]+]] = "felt.mul"(%[[IN]], %[[OUT]])
    %3 = "felt.mul"(%in, %out) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NEXT:      %[[ZERO:[0-9a-zA-Z_]+]] = "felt.const"() <{"value" = #felt<const 0>}>
    %c0 = "felt.const"() <{"value" = #felt<const 0> : !felt.type}> : () -> !felt.type
    // CHECK-NEXT:      "constrain.eq"(%[[ZPROD]], %[[ZERO]])
    "constrain.eq"(%3, %c0) : (!felt.type, !felt.type) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
