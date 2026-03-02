// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %pos = "llvm.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %neg = "llvm.constant"() <{ "value" = -4 : i32 }> : () -> i32
  "func.return"(%pos, %zero, %neg) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000008#32]
