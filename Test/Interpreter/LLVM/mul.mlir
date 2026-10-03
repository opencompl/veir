// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %rhs = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
    %x = "llvm.mul"(%lhs, %rhs) : (i32, i32) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000006#32]
