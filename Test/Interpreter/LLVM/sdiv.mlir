// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %negone = "llvm.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %x = "llvm.sdiv"(%lhs, %rhs) : (i32, i32) -> i32
  %y = "llvm.sdiv"(%lhs, %zero) : (i32, i32) -> i32
  %z = "llvm.sdiv"(%lhs, %negone) : (i32, i32) -> i32
  "func.return"(%x, %y, %z) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, poison, poison]
