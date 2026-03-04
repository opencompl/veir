// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "llvm.constant"() <{ "value" = 127 : i8 }> : () -> i8
  %negone = "llvm.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "llvm.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %x = "llvm.ashr"(%seven, %four) : (i8, i8) -> i8
  %y = "llvm.ashr"(%negone, %four) : (i8, i8) -> i8
  "func.return"(%x, %y) : (i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0xff#8]
