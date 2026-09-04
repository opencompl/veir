// RUN: VEIR_ROUNDTRIP

// CHECK:       "builtin.module"() ({
"builtin.module"() ({
  // CHECK:         "function.def"
  "function.def"() <{sym_name = "cmp_named_field", function_type = (!felt.type<"babybear">, !felt.type<"babybear">) -> ()}> ({
  // CHECK:       ^{{.*}}(%{{.*}}: !felt.type<"babybear">, %{{.*}}: !felt.type<"babybear">):
  ^bb0(%a: !felt.type<"babybear">, %b: !felt.type<"babybear">):
    // CHECK-NEXT:  %{{.*}} = "bool.cmp"(%{{.*}}, %{{.*}}) <{"predicate" = #bool<cmp ne>}> : (!felt.type<"babybear">, !felt.type<"babybear">) -> i1
    %0 = "bool.cmp"(%a, %b) <{predicate = #bool<cmp ne>}> : (!felt.type<"babybear">, !felt.type<"babybear">) -> i1
    // CHECK-NEXT:  "function.return"() : () -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
