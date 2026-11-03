// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "s"}> : () -> ()
    "llvm.unreachable"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat: only comdat selector symbols can appear in a comdat region
