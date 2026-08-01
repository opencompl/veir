// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `pdl.operation` produces an `!pdl.operation` handle, not an arbitrary type.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> i32
}) : () -> ()

// CHECK: pdl.operation: Expected the result to be of type '!pdl.operation'
