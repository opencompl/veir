// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 10 : i8 }> : () -> i8
  %rhs = "arith.constant"() <{ "value" = 13 : i8 }> : () -> i8
  %none = "arith.muli"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "arith.muli"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "arith.muli"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "arith.muli"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x82#8, poison, 0x82#8, poison]
