// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %seven = "arith.constant"() <{ "value" = 64 : i8 }> : () -> i8
  %negone = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %four = "arith.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %nine = "arith.constant"() <{ "value" = 9 : i8 }> : () -> i8
  %x = "arith.shrui"(%seven, %four) <{exact}> : (i8, i8) -> i8
  %y = "arith.shrui"(%negone, %four) <{exact}> : (i8, i8) -> i8
  %z = "arith.shrui"(%negone, %nine) <{exact}> : (i8, i8) -> i8
  "func.return"(%x, %y, %z) : (i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x04#8, poison, poison]
