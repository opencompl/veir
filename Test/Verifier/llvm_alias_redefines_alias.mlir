// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, linkage = #llvm.linkage<external>, sym_name = "a", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, linkage = #llvm.linkage<external>, sym_name = "a", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.alias: redefinition of symbol named 'a'
