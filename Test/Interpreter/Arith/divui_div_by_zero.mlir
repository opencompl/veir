// RUN: veir-interpret %s | filecheck %s

// Unsigned division with a concrete zero divisor is immediate UB.
"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %zero = "arith.constant"() <{ "value" = 0 : i32 }> : () -> i32
  %y = "arith.divui"(%lhs, %zero) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
