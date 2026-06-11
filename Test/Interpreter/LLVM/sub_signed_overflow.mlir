// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 200 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 80 : i8 }> : () -> i8
    %none = "llvm.sub"(%lhs, %rhs) : (i8, i8) -> i8
    %nsw = "llvm.sub"(%lhs, %rhs) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
    %nuw = "llvm.sub"(%lhs, %rhs) <{"overflowFlags" = 2 : i32}> : (i8, i8) -> i8
    %nuw_nsw = "llvm.sub"(%lhs, %rhs) <{"overflowFlags" = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x78#8, poison, 0x78#8, poison]
