// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %cpos = "arith.constant"() <{ "value" = 42 : i8 }> : () -> i8
  %cneg = "arith.constant"() <{ "value" = -1 : i8 }> : () -> i8
  %a = "arith.extui"(%cpos) <{nneg}> : (i8) -> i32
  %b = "arith.extui"(%cneg) <{nneg}> : (i8) -> i32
  "func.return"(%a, %b) : (i32, i32) -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32, poison]
