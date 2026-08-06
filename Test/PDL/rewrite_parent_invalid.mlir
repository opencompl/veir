// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A `pdl.rewrite` only ever terminates the body of a `pdl.pattern`.
"builtin.module"() ({
  "pdl.rewrite"() <{"name" = "rewriter", "operandSegmentSizes" = array<i32: 0, 0>}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: pdl.rewrite: Expected the parent operation to be a `pdl.pattern`
