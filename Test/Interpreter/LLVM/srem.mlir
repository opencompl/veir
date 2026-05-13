// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %negone = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %negthree = "llvm.mlir.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "llvm.mlir.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "llvm.srem"(%lhs, %rhs) : (i32, i32) -> i32
  %z = "llvm.srem"(%lhs, %negone) : (i32, i32) -> i32
  %a = "llvm.srem"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %z, %a) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32, 0x00000000#32, 0xffffffff#32]
