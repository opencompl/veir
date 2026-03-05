// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "arith.constant"() <{ "value" = 200 : i8 }> : () -> i8
  %rhs = "arith.constant"() <{ "value" = 80 : i8 }> : () -> i8
  %none = "arith.subi"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "arith.subi"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "arith.subi"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "arith.subi"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x78#8, poison, 0x78#8, poison]
