// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{comdat = @c::@s, function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.func: expected comdat symbol
