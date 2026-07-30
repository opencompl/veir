// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "main"}> ({
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %global = "llvm.mlir.addressof"() <{global_name = @missing}> : () -> !llvm.ptr
    "llvm.return"(%zero) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.addressof: symbol '@missing' does not name an llvm.mlir.global
