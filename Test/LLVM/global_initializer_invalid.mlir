// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 1 : i64, constant, dso_local, global_type = i32, linkage = #llvm.linkage<internal>, sym_name = "g", unnamed_addr = 0 : i64, visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    "llvm.return"(%0) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.return operand type does not match the global's declared global_type
