// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.constant"() <{ "value" = 200 : i8 }> : () -> i8
  %rhs = "llvm.constant"() <{ "value" = 80 : i8 }> : () -> i8
  %none = "llvm.sub"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "llvm.sub"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "llvm.sub"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "llvm.sub"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x78#8, poison, 0x78#8, poison]
