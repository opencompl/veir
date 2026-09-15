// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, linkage = #llvm.linkage<external>, sym_name = "a", tls_mode = 1 : i32, visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.alias: expected 'tls_mode' to be an i64 integer attribute between 0 and 4, but got 1 : i32
