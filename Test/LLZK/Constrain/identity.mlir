// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0(%a: !felt.type, %b: !felt.type, %i: i32):
  "constrain.eq"(%a, %b) : (!felt.type, !felt.type) -> ()
  "constrain.eq"(%i, %i) : (i32, i32) -> ()
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: !felt.type, %{{.*}}: !felt.type, %{{.*}}: i32):
// CHECK-NEXT:      "constrain.eq"(%{{.*}}, %{{.*}}) : (!felt.type, !felt.type) -> ()
// CHECK-NEXT:      "constrain.eq"(%{{.*}}, %{{.*}}) : (i32, i32) -> ()
// CHECK-NEXT: }) : () -> ()
