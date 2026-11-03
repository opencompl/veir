// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `pdl.replace` only appears inside the body of a `pdl.rewrite`.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  "pdl.replace"(%0, %0) <{"operandSegmentSizes" = array<i32: 1, 1, 0>}> : (!pdl.operation, !pdl.operation) -> ()
}) : () -> ()

// CHECK: pdl.replace: Expected the parent operation to be a `pdl.rewrite`
