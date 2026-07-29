// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A global's alignment must be a strictly positive power of two. Note that
// MLIR applies this constraint only to `llvm.mlir.global`: `llvm.load`,
// `llvm.store`, and `llvm.alloca` accept any 64-bit alignment.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 3 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.global: alignment attribute is not a power of 2
