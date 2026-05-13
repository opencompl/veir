// RUN: veir-interpret %s | filecheck %s

// Unsigned remainder by a poison divisor is immediate UB.
"builtin.module"() ({
  %lhs  = "arith.constant"() <{ "value" = 130 : i32 }> : () -> i32
  %neg1 = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
  %one  = "arith.constant"() <{ "value" = 1 : i32 }> : () -> i32
  %poison = "arith.addi"(%neg1, %one) <{nuw}> : (i32, i32) -> i32
  %y = "arith.remui"(%lhs, %poison) : (i32, i32) -> i32
  "func.return"(%y) : (i32) -> ()
}) : () -> ()

// CHECK: Undefined behavior
