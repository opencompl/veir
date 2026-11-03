// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// The `root` operand of a `pdl.rewrite` is an `!pdl.operation` handle.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    "pdl.rewrite"(%0) <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 1, 0>}> ({
    }) : (!pdl.type) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.rewrite: Expected the `root` operand to be of type '!pdl.operation'
