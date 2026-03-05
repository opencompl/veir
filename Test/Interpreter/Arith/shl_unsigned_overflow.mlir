// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 255 : i8 }> : () -> i8
  %rhs = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
  %none = "arith.shli"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "arith.shli"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "arith.shli"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "arith.shli"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0xe0#8, 0xe0#8, poison, poison]
