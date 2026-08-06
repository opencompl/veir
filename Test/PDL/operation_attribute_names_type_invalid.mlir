// RUN: not veir-opt %s 2>&1 | filecheck %s

// `attributeValueNames` holds attribute names, which are strings.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [0 : i32], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
}) : () -> ()

// CHECK: pdl.operation: expected 'attributeValueNames' to hold string attributes, but got 0 : i32
