// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 150 : i8 }> : () -> i8
  %rhs = "llvm.constant"() <{ "value" = 100 : i8 }> : () -> i8
  %none = "llvm.mul"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "llvm.mul"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "llvm.mul"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "llvm.mul"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x98#8, poison, poison, poison]
