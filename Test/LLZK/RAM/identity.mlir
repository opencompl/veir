// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0(%addr: index, %val: !felt.type):
  "ram.store"(%addr, %val) : (index, !felt.type) -> ()
  %0 = "ram.load"(%addr) : (index) -> !felt.type
  "ram.store"(%addr, %0) : (index, !felt.type) -> ()
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: index, %{{.*}}: !felt.type):
// CHECK-NEXT:      "ram.store"(%{{.*}}, %{{.*}}) : (index, !felt.type) -> ()
// CHECK-NEXT:      %{{.*}} = "ram.load"(%{{.*}}) : (index) -> !felt.type
// CHECK-NEXT:      "ram.store"(%{{.*}}, %{{.*}}) : (index, !felt.type) -> ()
// CHECK-NEXT: }) : () -> ()
