// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `pdl.result` produces an `!pdl.value` handle, not an arbitrary type.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  %1 = "pdl.result"(%0) <{"index" = 0 : i32}> : (!pdl.operation) -> i32
}) : () -> ()

// CHECK: pdl.result: Expected the result to be of type '!pdl.value'
