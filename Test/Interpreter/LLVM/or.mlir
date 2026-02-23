// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 8 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 4 : i32 }> : () -> i32
  %x = "llvm.or"(%lhs, %rhs) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[value 0x0000000c#32]
