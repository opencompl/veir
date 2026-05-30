// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 150 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %none = "llvm.mul"(%lhs, %rhs) : (i8, i8) -> i8
    %nsw = "llvm.mul"(%lhs, %rhs) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
    %nuw = "llvm.mul"(%lhs, %rhs) <{"overflowFlags" = 2 : i32}> : (i8, i8) -> i8
    %nuw_nsw = "llvm.mul"(%lhs, %rhs) <{"overflowFlags" = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x98#8, poison, poison, poison]
