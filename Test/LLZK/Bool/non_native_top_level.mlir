// RUN: VEIR_ROUNDTRIP

// LLZK permits NotFieldNative operations outside a function.def.
// CHECK:       "builtin.module"() ({
"builtin.module"() ({
// CHECK-NEXT:  ^{{.*}}(%{{.*}}: i1, %{{.*}}: i1):
^bb0(%a: i1, %b: i1):
  // CHECK-NEXT:  %{{.*}} = "bool.and"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
  %0 = "bool.and"(%a, %b) : (i1, i1) -> i1
// CHECK-NEXT:  }) : () -> ()
}) : () -> ()
