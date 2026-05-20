// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0(%i: i32, %b: i1, %f: !felt.type):
  %0 = "cast.tofelt"(%i) : (i32) -> !felt.type
  %1 = "cast.tofelt"(%b) : (i1) -> !felt.type
  %2 = "cast.toindex"(%f) : (!felt.type) -> index
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: i32, %{{.*}}: i1, %{{.*}}: !felt.type):
// CHECK-NEXT:      %{{.*}} = "cast.tofelt"(%{{.*}}) : (i32) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "cast.tofelt"(%{{.*}}) : (i1) -> !felt.type
// CHECK-NEXT:      %{{.*}} = "cast.toindex"(%{{.*}}) : (!felt.type) -> index
// CHECK-NEXT: }) : () -> ()
