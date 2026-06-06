// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
    %rhs = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
    %x = "llvm.sdiv"(%lhs, %rhs) <{exact}> : (i32, i32) -> i32
    "func.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
