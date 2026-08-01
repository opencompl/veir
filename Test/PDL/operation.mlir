// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  // Define an operation with no constraints:
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  // Define an operation with a name:
  %1 = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  // Define an operation with operands, attributes and result types:
  %2 = "pdl.operand"() : () -> !pdl.value
  %3 = "pdl.operand"() : () -> !pdl.value
  %4 = "pdl.attribute"() : () -> !pdl.attribute
  %5 = "pdl.type"() : () -> !pdl.type
  %6 = "pdl.operation"(%2, %3, %4, %5) <{"attributeValueNames" = ["attrA"], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 2, 1, 1>}> : (!pdl.value, !pdl.value, !pdl.attribute, !pdl.type) -> !pdl.operation
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
// CHECK-NEXT:     %{{.*}} = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
// CHECK-NEXT:     %[[v0:.*]] = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:     %[[v1:.*]] = "pdl.operand"() : () -> !pdl.value
// CHECK-NEXT:     %[[a0:.*]] = "pdl.attribute"() : () -> !pdl.attribute
// CHECK-NEXT:     %[[t0:.*]] = "pdl.type"() : () -> !pdl.type
// CHECK-NEXT:     %{{.*}} = "pdl.operation"(%[[v0]], %[[v1]], %[[a0]], %[[t0]]) <{"attributeValueNames" = ["attrA"], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 2, 1, 1>}> : (!pdl.value, !pdl.value, !pdl.attribute, !pdl.type) -> !pdl.operation
// CHECK-NEXT: }) : () -> ()
