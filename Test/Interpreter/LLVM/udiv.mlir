// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %rhs = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %negthree = "llvm.mlir.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "llvm.mlir.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "llvm.udiv"(%lhs, %rhs) : (i32, i32) -> i32
  %a = "llvm.udiv"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %a) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002b#32, 0x00000000#32]
