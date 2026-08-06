// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The `parent` operand of a `pdl.result` is an `!pdl.operation` handle. The
// handle fed in here comes from a `pdl.result` rather than a `pdl.operand`,
// which would need a `pdl.pattern` parent to satisfy MLIR and so would make
// `MLIR_INVALID` above pass for the wrong reason.
"builtin.module"() ({
  %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  %1 = "pdl.result"(%0) <{"index" = 0 : i32}> : (!pdl.operation) -> !pdl.value
  %2 = "pdl.result"(%1) <{"index" = 0 : i32}> : (!pdl.value) -> !pdl.value
}) : () -> ()

// CHECK: pdl.result: Expected the `parent` operand to be of type '!pdl.operation'
