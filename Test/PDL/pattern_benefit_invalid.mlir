// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The `benefit` of a `pdl.pattern` is a 16-bit attribute.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i32}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.pattern: Expected 'benefit' to be a 16-bit signless integer attribute
