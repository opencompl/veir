// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A global is initialized either by the `value` attribute or by its body
// region, never by both.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
    %c = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    "llvm.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.global: cannot have both initializer value and region
