// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 8 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 12 : i32 }> : () -> i32
  %x = "llvm.and"(%lhs, %rhs) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[value 0x00000008#32]
