// RUN: VEIR_ROUNDTRIP

// The `pdl` handle types are nullary and round-trip as-is.
"builtin.module"() ({
  %0 = "test.test"() : () -> !pdl.attribute
  %1 = "test.test"() : () -> !pdl.operation
  %2 = "test.test"() : () -> !pdl.value
  %3 = "test.test"() : () -> !pdl.type
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.attribute
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.operation
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.value
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.type
// CHECK-NEXT: }) : () -> ()
