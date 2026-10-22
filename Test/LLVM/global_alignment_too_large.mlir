// RUN: not veir-opt %s 2>&1 | filecheck %s

// LLVM's largest alignment is 2^32. MLIR accepts a larger one, so there is no
// MLIR_INVALID line; VeIR rejects it, as LLVM would.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 8589934592 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.global: alignment attribute exceeds the largest alignment LLVM supports, 2^32
