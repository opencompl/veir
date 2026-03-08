// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %c127 = "arith.constant"() <{ "value" = 127 : i8 }> : () -> i8
  %cneg = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %a = "arith.extsi"(%c127) : (i8) -> i32
  %b = "arith.extsi"(%cneg) : (i8) -> i32
  "func.return"(%a, %b) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000007f#32, 0xffffffff#32]
