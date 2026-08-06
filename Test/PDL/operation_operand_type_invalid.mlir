// RUN: not veir-opt %s 2>&1 | filecheck %s

// The `operandValues` group of a `pdl.operation` holds `!pdl.value` handles, so
// an `!pdl.attribute` handle in that group is rejected.
"builtin.module"() ({
  %0 = "pdl.attribute"() : () -> !pdl.attribute
  %1 = "pdl.operation"(%0) <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!pdl.attribute) -> !pdl.operation
}) : () -> ()

// CHECK: pdl.operation: Expected operand 0 to be of type '!pdl.value'
