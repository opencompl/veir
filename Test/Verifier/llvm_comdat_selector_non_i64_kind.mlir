// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i32, sym_name = "s"}> : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.comdat_selector: expected 'comdat' to be an i64 integer attribute, but got 0 : i32
