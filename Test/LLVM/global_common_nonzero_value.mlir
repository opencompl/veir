// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `common` linkage merges symbols at link time, so its initializer must be
// zero. See `global_initializer_forms.mlir` for the accepted zero case.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<common>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.global: expected zero value for 'common' linkage
