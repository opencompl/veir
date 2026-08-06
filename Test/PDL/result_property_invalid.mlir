// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `index` is required on a `pdl.result`.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  %1 = "pdl.result"(%0) : (!pdl.operation) -> !pdl.value
}) : () -> ()

// CHECK: pdl.result: missing 'index' property
