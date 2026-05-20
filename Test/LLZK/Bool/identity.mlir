// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
^bb0(%a: i1, %b: i1):
  %0 = "bool.and"(%a, %b) : (i1, i1) -> i1
  %1 = "bool.or"(%a, %b) : (i1, i1) -> i1
  %2 = "bool.xor"(%a, %b) : (i1, i1) -> i1
  %3 = "bool.not"(%a) : (i1) -> i1
  "bool.assert"(%0) : (i1) -> ()
  "bool.assert"(%0) <{msg = "expected true"}> : (i1) -> ()
}) : () -> ()


// CHECK:       "builtin.module"() ({
// CHECK-NEXT:    ^{{.*}}(%{{.*}}: i1, %{{.*}}: i1):
// CHECK-NEXT:      %{{.*}} = "bool.and"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.or"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.xor"(%{{.*}}, %{{.*}}) : (i1, i1) -> i1
// CHECK-NEXT:      %{{.*}} = "bool.not"(%{{.*}}) : (i1) -> i1
// CHECK-NEXT:      "bool.assert"(%{{.*}}) : (i1) -> ()
// CHECK-NEXT:      "bool.assert"(%{{.*}}) <{"msg" = "expected true"}> : (i1) -> ()
// CHECK-NEXT: }) : () -> ()
