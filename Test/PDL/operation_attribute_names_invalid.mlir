// RUN: not veir-opt %s 2>&1 | filecheck %s

// `attributeValueNames` names the attribute operands positionally, so it must
// hold exactly one name per attribute operand.
"builtin.module"() ({
  %0 = "pdl.attribute"() : () -> !pdl.attribute
  %1 = "pdl.operation"(%0) <{"attributeValueNames" = ["attrA", "attrB"], "operandSegmentSizes" = array<i32: 0, 1, 0>}> : (!pdl.attribute) -> !pdl.operation
}) : () -> ()

// CHECK: pdl.operation: Expected the same number of attribute values and attribute names, got 1 values and 2 names
