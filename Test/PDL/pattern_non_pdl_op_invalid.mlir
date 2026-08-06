// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `pdl.pattern` body describes a pattern, so it holds only `pdl` operations.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %1 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%1) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.pattern: expected only `pdl` operations within the pattern body, but got 'arith.constant'
