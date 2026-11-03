// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The body of a `pdl.pattern` must be terminated by a `pdl.rewrite`.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.pattern: Expected the body to terminate with a `pdl.rewrite`
