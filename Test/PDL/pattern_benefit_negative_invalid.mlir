// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// MLIR confines `benefit` to non-negative values.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = -1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.pattern: Expected 'benefit' to be non-negative, but got -1
