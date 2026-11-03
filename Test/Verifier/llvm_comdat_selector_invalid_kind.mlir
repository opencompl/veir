// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 5 : i64, sym_name = "s"}> : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat_selector: invalid comdat kind 5
