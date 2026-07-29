// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.global: 'alignment' must be a 64-bit signless integer attribute
