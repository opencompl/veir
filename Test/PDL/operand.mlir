// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  // Define an external operand:
  %0 = "pdl.operand"() : () -> !pdl.value
  // Define an external operand with an expected type:
  %1 = "pdl.type"() <{"constantType" = i32}> : () -> !pdl.type
  %2 = "pdl.operand"(%1) : (!pdl.type) -> !pdl.value
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:     %{{.*}} = "pdl.type"() <{"constantType" = i32}> : () -> !pdl.type
// CHECK-NEXT:     %{{.*}} = "pdl.operand"(%{{.*}}) : (!pdl.type) -> !pdl.value
// CHECK-NEXT: }) : () -> ()
