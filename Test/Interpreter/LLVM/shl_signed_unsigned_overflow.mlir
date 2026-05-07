// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  %lhs = "llvm.mlir.constant"() <{ "value" = 4 : i8 }> : () -> i8
  %rhs = "llvm.mlir.constant"() <{ "value" = 6 : i8 }> : () -> i8
  %none = "llvm.shl"(%lhs, %rhs) : (i8, i8) -> i8
  %nsw = "llvm.shl"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
  %nuw = "llvm.shl"(%lhs, %rhs) <{nuw}> : (i8, i8) -> i8
  %nuw_nsw = "llvm.shl"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
  "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8, poison, poison, poison]
