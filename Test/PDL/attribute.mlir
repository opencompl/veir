// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  // Define an attribute:
  %0 = "pdl.attribute"() : () -> !pdl.attribute
  // Define an attribute with an expected value:
  %1 = "pdl.attribute"() <{"value" = "hello"}> : () -> !pdl.attribute
  // Define an attribute with an expected type. `test.test` stands in for
  // `pdl.type`, which is not modelled yet:
  %2 = "test.test"() : () -> !pdl.type
  %3 = "pdl.attribute"(%2) : (!pdl.type) -> !pdl.attribute
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"() : () -> !pdl.attribute
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"() <{"value" = "hello"}> : () -> !pdl.attribute
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.type
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"(%{{.*}}) : (!pdl.type) -> !pdl.attribute
// CHECK-NEXT: }) : () -> ()
