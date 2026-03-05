// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %zero = "llvm.constant"() <{ "value" = 0 : i8 }> : () -> i8
  %seven = "llvm.constant"() <{ "value" = 127 : i8 }> : () -> i8
  %negone = "llvm.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "llvm.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %nine = "llvm.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %thirtytwo = "llvm.constant"() <{ "value" = 32 : i8 }> : () -> i8
  %x = "llvm.lshr"(%seven, %four) : (i8, i8) -> i8
  %y = "llvm.lshr"(%negone, %four) : (i8, i8) -> i8
  %z = "llvm.lshr"(%negone, %nine) : (i8, i8) -> i8
  %p = "llvm.lshr"(%zero, %thirtytwo) : (i8, i8) -> i8
  "func.return"(%x, %y, %z, %p) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0x0f#8, poison, poison]
