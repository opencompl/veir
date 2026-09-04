// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "named_field", function_type = (i1) -> ()}> ({
  // CHECK:       ^{{.*}}(%{{.*}}: i1):
  ^bb0(%value: i1):
    // CHECK-NEXT:  %{{.*}} = "cast.tofelt"(%{{.*}}) <{"overflow" = #cast<overflow assert>}> : (i1) -> !felt.type<"bn128">
    %0 = "cast.tofelt"(%value) : (i1) -> !felt.type<"bn128">
    // CHECK-NEXT:  "function.return"() : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
