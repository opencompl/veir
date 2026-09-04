// RUN: VEIR_ROUNDTRIP

// LLZK permits NotFieldNative operations outside a function.def.
// CHECK:       "builtin.module"() ({
"builtin.module"() ({
// CHECK-NEXT:  ^{{.*}}(%{{.*}}: !felt.type):
^bb0(%value: !felt.type):
  // CHECK-NEXT:  %{{.*}} = "cast.toindex"(%{{.*}}) <{"overflow" = #cast<overflow assert>}> : (!felt.type) -> index
  %0 = "cast.toindex"(%value) : (!felt.type) -> index
// CHECK-NEXT:  }) : () -> ()
}) : () -> ()
