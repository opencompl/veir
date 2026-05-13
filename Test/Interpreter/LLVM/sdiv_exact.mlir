// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %x = "llvm.sdiv"(%lhs, %rhs) <{exact}> : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
