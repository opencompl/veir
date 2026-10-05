// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat: region should have exactly one block
