// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// MLIR gives `pdl.rewrite` `SingleBlock`, so its body holds at most one block.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    "pdl.rewrite"(%0) <{"operandSegmentSizes" = array<i32: 1, 0>}> ({
      ^bb0():
        %1 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
      ^bb1():
        %2 = "pdl.operation"() <{"attributeValueNames" = [], "operandSegmentSizes" = array<i32: 0, 0, 0>}> : () -> !pdl.operation
    }) : (!pdl.operation) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.rewrite: Expected the rewrite region to contain at most 1 block
