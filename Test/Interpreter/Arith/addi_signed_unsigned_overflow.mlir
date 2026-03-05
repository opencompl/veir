// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 150 : i8 }> : () -> i8
  %rhs = "arith.constant"() <{ "value" = 150 : i8 }> : () -> i8
  %none = "arith.addi"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "arith.addi"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "arith.addi"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "arith.addi"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x2c#8, poison, poison, poison]
