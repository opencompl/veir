// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "llvm.constant"() <{ "value" = 64 : i8 }> : () -> i8
  %negone = "llvm.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "llvm.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %nine = "llvm.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %x = "llvm.ashr"(%seven, %four) <{exact}> : (i8, i8) -> i8
  %y = "llvm.ashr"(%negone, %four) <{exact}> : (i8, i8) -> i8
  %z = "llvm.ashr"(%negone, %nine) <{exact}> : (i8, i8) -> i8
  "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x04#8, poison, poison]
