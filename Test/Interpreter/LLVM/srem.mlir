// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "llvm.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %zero = "llvm.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %negone = "llvm.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %negthree = "llvm.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "llvm.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "llvm.srem"(%lhs, %rhs) : (i32, i32) -> i32
  %y = "llvm.srem"(%lhs, %zero) : (i32, i32) -> i32
  %z = "llvm.srem"(%lhs, %negone) : (i32, i32) -> i32
  %a = "llvm.srem"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %y, %z) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32, poison, 0x00000000#32]
