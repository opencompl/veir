// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %x = "llvm.udiv"(%lhs, %rhs) : (i32, i32) -> i32
  %y = "llvm.udiv"(%lhs, %zero) : (i32, i32) -> i32
  "func.return"(%x) : (i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002b#32, poison]
