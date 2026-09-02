// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"() <{"function_type" = (!felt.type, !felt.type, index) -> (), "sym_name" = "constrain_identity"}> ({
  "function.def"() <{sym_name = "constrain_identity", function_type = (!felt.type, !felt.type, index) -> ()}> ({
  // CHECK-NEXT:    ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type, %{{.*}}: index):
  ^bb0(%a: !felt.type, %b: !felt.type, %i: index):
    // CHECK-NEXT:      "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
    "constrain.eq"(%a, %b) : (!felt.type, !felt.type) -> ()
    // CHECK-NEXT:      "constrain.eq"(%{{.*}}, %{{.*}}) : (index, index) -> ()
    "constrain.eq"(%i, %i) : (index, index) -> ()
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK-NEXT:    }) {function.allow_constraint} : () -> ()
  }) {function.allow_constraint} : () -> ()
}) : () -> ()
