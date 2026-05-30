// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 10 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 4 : i8 }> : () -> i8
    %none = "llvm.shl"(%lhs, %rhs) : (i8, i8) -> i8
    %nsw = "llvm.shl"(%lhs, %rhs) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
    %nuw = "llvm.shl"(%lhs, %rhs) <{"overflowFlags" = 2 : i32}> : (i8, i8) -> i8
    %nuw_nsw = "llvm.shl"(%lhs, %rhs) <{"overflowFlags" = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xa0#8, poison, 0xa0#8, poison]
