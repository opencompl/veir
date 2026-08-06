// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  // Define an attribute:
  %0 = "pdl.attribute"() : () -> !pdl.attribute
  // Define an attribute with an expected value:
  %1 = "pdl.attribute"() <{"value" = "hello"}> : () -> !pdl.attribute
  // Define an attribute with an expected type:
  %2 = "pdl.type"() : () -> !pdl.type
  %3 = "pdl.attribute"(%2) : (!pdl.type) -> !pdl.attribute
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"() : () -> !pdl.attribute
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"() <{"value" = "hello"}> : () -> !pdl.attribute
// CHECK-NEXT:     %{{.*}} = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:     %{{.*}} = "pdl.attribute"(%{{.*}}) : (!pdl.type) -> !pdl.attribute
// CHECK-NEXT: }) : () -> ()
