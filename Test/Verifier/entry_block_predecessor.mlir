// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A region is entered only through its entry block, so that block may not have
// predecessors: ^bb1 branching back to ^bb0 would re-enter the region. Mirrors
// the "Verify the first block has no predecessors" check in
// `OperationVerifier::verifyOnEntrance` (`mlir/lib/IR/Verifier.cpp`).

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> ()}> ({
  ^bb0:
    "cf.br"() [^bb1] : () -> ()
  ^bb1:
    "cf.br"() [^bb0] : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: entry block of region may not have predecessors
