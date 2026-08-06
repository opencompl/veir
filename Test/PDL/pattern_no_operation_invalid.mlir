// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A pattern that matches no operation matches nothing.
"builtin.module"() ({
  "pdl.pattern"() <{"benefit" = 1 : i16}> ({
    %0 = "pdl.type"() : () -> !pdl.type
    "pdl.rewrite"() <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 0, 0>}> ({
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.pattern: the pattern must contain at least one `pdl.operation`
