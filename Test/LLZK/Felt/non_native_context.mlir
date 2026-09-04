// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "allowed", function_type = (!felt.type, !felt.type) -> (!felt.type)}> ({
  // CHECK:       ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type):
  ^bb0(%base: !felt.type, %exponent: !felt.type):
    // CHECK-NEXT:  %{{.*}} = "felt.pow"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> !felt.type
    %0 = "felt.pow"(%base, %exponent) : (!felt.type, !felt.type) -> !felt.type
    // CHECK-NEXT:  "function.return"(%{{.*}}) : (!felt.type) -> ()
    "function.return"(%0) : (!felt.type) -> ()
  // CHECK-NEXT:  }) {function.allow_non_native_field_ops} : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
