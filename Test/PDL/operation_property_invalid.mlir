// RUN: not veir-opt %s 2>&1 | filecheck %s

// `attributeValueNames` is required on a `pdl.operation`.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
}) : () -> ()

// CHECK: pdl.operation: missing 'attributeValueNames' property
