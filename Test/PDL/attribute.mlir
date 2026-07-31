// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  // Define an attribute:
  %0 = "pdl.attribute"() : () -> !pdl.attribute
  // Define an attribute with an expected value:
  %1 = "pdl.attribute"() <{"value" = "hello"}> : () -> !pdl.attribute
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"() : () -> !pdl.attribute
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"() <{"value" = "hello"}> : () -> !pdl.attribute
// CHECK-NEXT: }) : () -> ()
