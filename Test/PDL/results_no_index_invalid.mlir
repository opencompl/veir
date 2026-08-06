// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// Without an index a `pdl.results` yields the whole result range, not one value.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "opName" = "foo.op", "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    %1 = "pdl.results"(%0) : (!pdl.operation) -> !pdl.value
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.results: Expected a '!pdl.range<value>' result type when no index is specified
