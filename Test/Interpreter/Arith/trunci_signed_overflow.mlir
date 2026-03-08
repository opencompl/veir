// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  // 127 fits in i8 signed: sext(trunc(127)) == 127, no poison
  %c127 = "arith.constant"() <{ "value" = 127 : i32 }> : () -> i32
  // 128 does not fit in i8 signed: sext(trunc(128)) == -128 != 128, poison
  %c128 = "arith.constant"() <{ "value" = 128 : i32 }> : () -> i32
  %a = "arith.trunci"(%c127) <{nsw}> : (i32) -> i8
  %b = "arith.trunci"(%c128) <{nsw}> : (i32) -> i8
  "func.return"(%a, %b) : (i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x7f#8, poison]
