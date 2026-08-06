// RUN: not veir-opt %s 2>&1 | filecheck %s

// `operandSegmentSizes` must account for every operand.
"builtin.module"() ({
  %0 = "pdl.operand"() : () -> !pdl.value
  %1 = "pdl.operation"(%0) <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : (!pdl.value) -> !pdl.operation
}) : () -> ()

// CHECK: pdl.operation: operandSegmentSizes describes 0 operands, got 1
