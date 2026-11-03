// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
  ^bb0(%x: i32):
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "s"}> : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat: region should have no arguments
