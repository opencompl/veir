// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The `index` of a `pdl.result` is a 32-bit integer attribute.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  %1 = "pdl.result"(%0) <{"index" = 0 : i64}> : (!pdl.operation) -> !pdl.value
}) : () -> ()

// CHECK: pdl.result: Expected 'index' to be a 32-bit signless integer attribute
