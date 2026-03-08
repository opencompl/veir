// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %c255 = "arith.constant"() <{ "value" = 255 : i8 }> : () -> i8
  %cneg = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %a = "arith.extui"(%c255) : (i8) -> i32
  %b = "arith.extui"(%cneg) : (i8) -> i32
  "func.return"(%a, %b) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000ff#32, 0x000000ff#32]
