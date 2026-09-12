// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "s"}> : () -> ()
    "llvm.comdat_selector"() <{comdat = 1 : i64, sym_name = "s"}> : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat_selector: redefinition of symbol named 's'
