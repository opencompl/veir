// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "llvm.mlir.constant"() <{ "value" = 127 : i8 }> : () -> i8
  %negone = "llvm.mlir.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "llvm.mlir.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %nine = "llvm.mlir.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %x = "llvm.ashr"(%seven, %four) : (i8, i8) -> i8
  %y = "llvm.ashr"(%negone, %four) : (i8, i8) -> i8
  %z = "llvm.ashr"(%negone, %nine) : (i8, i8) -> i8
  "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0xff#8, poison]
