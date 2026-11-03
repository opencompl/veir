// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  %0 = "pdl.type"() : () -> !pdl.type
  %1 = "pdl.operation"(%0, %0) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 2>}> : (!pdl.type, !pdl.type) -> !pdl.operation
  // Extract a result:
  %2 = "pdl.result"(%1) <{"index" = 1 : i32}> : (!pdl.operation) -> !pdl.value
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %[[t:.*]] = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:     %[[op:.*]] = "pdl.operation"(%[[t]], %[[t]]) <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 2>}> : (!pdl.type, !pdl.type) -> !pdl.operation
// CHECK-NEXT:     %{{.*}} = "pdl.result"(%[[op]]) <{"index" = 1 : i32}> : (!pdl.operation) -> !pdl.value
// CHECK-NEXT: }) : () -> ()
