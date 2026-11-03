// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "main"}> ({
    %bad = "llvm.mlir.addressof"() <{global_name = @g}> : () -> i32
    "llvm.return"(%bad) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.addressof: Expected result to have !llvm.ptr type
