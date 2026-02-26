// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %x = "llvm.mul"(%lhs, %rhs) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000006#32]
