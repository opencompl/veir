// RUN: veir-interpret %s | filecheck %s

// `remsi intMin, -1` is immediate UB (signed overflow in the implicit division).
"builtin.module"() ({
  %intmin = "arith.constant"() <{ "value" = -2147483648 : i32 }> : () -> i32
  %negone = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %y = "arith.remsi"(%intmin, %negone) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
