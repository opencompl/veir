// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  %0 = "test.test"() : () -> !pdl.range<attribute>
  %1 = "test.test"() : () -> !pdl.range<operation>
  %2 = "test.test"() : () -> !pdl.range<type>
  %3 = "test.test"() : () -> !pdl.range<value>
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.range<attribute>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.range<operation>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.range<type>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !pdl.range<value>
// CHECK-NEXT: }) : () -> ()
