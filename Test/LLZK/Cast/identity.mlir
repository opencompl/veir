// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"() <{"function_type" = (index, i1, !felt.type) -> (), "sym_name" = "cast_identity"}> ({
  "function.def"() <{sym_name = "cast_identity", function_type = (index, i1, !felt.type) -> ()}> ({
  // CHECK-NEXT:    ^{{.*}}(%{{.*}}: index, %{{.*}}: i1, %{{.*}}: !felt.type):
  ^bb0(%i: index, %b: i1, %f: !felt.type):
    // CHECK-NEXT:      %{{.*}} = "cast.tofelt"(%{{.*}}) : (index) -> !felt.type
    %0 = "cast.tofelt"(%i) : (index) -> !felt.type
    // CHECK-NEXT:      %{{.*}} = "cast.tofelt"(%{{.*}}) : (i1) -> !felt.type
    %1 = "cast.tofelt"(%b) : (i1) -> !felt.type
    // CHECK-NEXT:      %{{.*}} = "cast.toindex"(%{{.*}}) : (!felt.type) -> index
    %2 = "cast.toindex"(%f) : (!felt.type) -> index
    // CHECK-NEXT:      "function.return"() : () -> ()
    "function.return"() : () -> ()
  // CHECK-NEXT:    }) {function.allow_non_native_field_ops} : () -> ()
  }) {function.allow_non_native_field_ops} : () -> ()
}) : () -> ()
