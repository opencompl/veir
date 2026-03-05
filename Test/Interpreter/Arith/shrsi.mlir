// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "arith.constant"() <{ "value" = 127 : i8 }> : () -> i8
  %negone = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "arith.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %nine = "arith.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %x = "arith.shrsi"(%seven, %four) : (i8, i8) -> i8
  %y = "arith.shrsi"(%negone, %four) : (i8, i8) -> i8
  %z = "arith.shrsi"(%negone, %nine) : (i8, i8) -> i8
  "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0xff#8, poison]
