// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %c255 = "arith.constant"() <{ "value" = 255 : i32 }> : () -> i32
  %c256 = "arith.constant"() <{ "value" = 256 : i32 }> : () -> i32
  %cneg = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %a = "arith.trunci"(%c255) : (i32) -> i8
  %b = "arith.trunci"(%c256) : (i32) -> i8
  %c = "arith.trunci"(%cneg) : (i32) -> i16
  "func.return"(%a, %b, %c) : (i8, i8, i16) -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, 0x00#8, 0xffff#16]
