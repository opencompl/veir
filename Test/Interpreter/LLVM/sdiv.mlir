// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
  %rhs = "llvm.mlir.constant"() <{ "value" = 2 : i32 }> : () -> i32
  %negone = "llvm.mlir.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %negthree = "llvm.mlir.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "llvm.mlir.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "llvm.sdiv"(%lhs, %rhs) : (i32, i32) -> i32
  %z = "llvm.sdiv"(%lhs, %negone) : (i32, i32) -> i32
  %a = "llvm.sdiv"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %z, %a) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32, 0xfffffff9#32, 0x00000001#32]
