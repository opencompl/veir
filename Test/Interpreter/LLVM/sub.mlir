// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 5 : i32 }> : () -> i32
    %rhs = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
    %x = "llvm.sub"(%lhs, %rhs) : (i32, i32) -> i32
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000002#32]
