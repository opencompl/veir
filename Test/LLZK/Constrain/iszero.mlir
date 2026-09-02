// RUN: VEIR_ROUNDTRIP

// Circomlib IsZero constraint system, adapted from
// llzk-lib/test/Conversions/llzk_to_smt_no_cf_iszero.llzk:
//   out = -in * inv + 1
//   in * out = 0

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "main", function_type = () -> ()}> ({
    %in = "felt.const"() <{value = #felt<const 2 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %out = "felt.const"() <{value = #felt<const 0 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    %inv = "felt.const"() <{value = #felt<const 1006632961 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK:           %[[NEG:[0-9a-zA-Z_]+]] = "felt.neg"(%{{.*}})
    %0 = "felt.neg"(%in) : (!felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NEXT:      %[[PROD:[0-9a-zA-Z_]+]] = "felt.mul"(%[[NEG]], %{{.*}})
    %1 = "felt.mul"(%0, %inv) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    %c1 = "felt.const"() <{value = #felt<const 1 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK:           %[[SUM:[0-9a-zA-Z_]+]] = "felt.add"(%[[PROD]], %{{.*}})
    %2 = "felt.add"(%1, %c1) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    // CHECK-NEXT:      "constrain.eq"(%{{.*}}, %[[SUM]])
    "constrain.eq"(%out, %2) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
    %3 = "felt.mul"(%in, %out) : (!felt.type<"babybear">, !felt.type<"babybear">) -> !felt.type<"babybear">
    %c0 = "felt.const"() <{value = #felt<const 0 : <"babybear">> : !felt.type<"babybear">}> : () -> !felt.type<"babybear">
    // CHECK:           "constrain.eq"(%{{.*}}, %{{.*}})
    "constrain.eq"(%3, %c0) : (!felt.type<"babybear">, !felt.type<"babybear">) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  }) {function.allow_constraint, function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
