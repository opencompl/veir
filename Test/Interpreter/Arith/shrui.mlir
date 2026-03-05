// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %zero = "arith.constant"() <{ "value" = 0 : i8 }> : () -> i8
  %seven = "arith.constant"() <{ "value" = 127 : i8 }> : () -> i8
  %negone = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "arith.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %nine = "arith.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %thirtytwo = "arith.constant"() <{ "value" = 32 : i8 }> : () -> i8
  %x = "arith.shrui"(%seven, %four) : (i8, i8) -> i8
  %y = "arith.shrui"(%negone, %four) : (i8, i8) -> i8
  %z = "arith.shrui"(%negone, %nine) : (i8, i8) -> i8
  %p = "arith.shrui"(%zero, %thirtytwo) : (i8, i8) -> i8
  "func.return"(%x, %y, %z, %p) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8, 0x0f#8, poison, poison]
