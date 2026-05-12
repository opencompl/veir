// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %rhs = "llvm.mlir.constant"() <{ "value" = 3 : i32 }> : () -> i32
  %zero = "llvm.mlir.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %negthree = "llvm.mlir.constant"() <{ "value" = -3 : i32 }> : () -> i32
  %negtwo = "llvm.mlir.constant"() <{ "value" = -2 : i32 }> : () -> i32
  %x = "llvm.urem"(%lhs, %rhs) : (i32, i32) -> i32
  %y = "llvm.urem"(%lhs, %zero) : (i32, i32) -> i32
  %a = "llvm.urem"(%negthree, %negtwo) : (i32, i32) -> i32
  "func.return"(%x, %y, %a) : (i32, i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32, poison, 0xfffffffd#32]
