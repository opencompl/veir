// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.comdat"() <{sym_name = "c"}> ({
    "llvm.comdat_selector"() <{comdat = 0 : i64, sym_name = "s"}> : () -> ()
  }) : () -> ()
  "llvm.func"() <{comdat = @c::@c, function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.func: expected comdat symbol
