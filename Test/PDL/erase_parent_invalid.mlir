// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `pdl.erase` only appears inside the body of a `pdl.rewrite`.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  "pdl.erase"(%0) : (!pdl.operation) -> ()
}) : () -> ()

// CHECK: pdl.erase: Expected the parent operation to be a `pdl.rewrite`
