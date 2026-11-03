// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "s"}> : () -> ()
  ^bb1:
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "t"}> : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat: region should have exactly one block
