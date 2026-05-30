// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %lhs = "llvm.mlir.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %rhs = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %none = "llvm.add"(%lhs, %rhs) : (i8, i8) -> i8
    %nsw = "llvm.add"(%lhs, %rhs) <{nsw}> : (i8, i8) -> i8
    %nuw = "llvm.add"(%lhs, %rhs) <{"overflowFlags" = 2 : i32}> : (i8, i8) -> i8
    %nuw_nsw = "llvm.add"(%lhs, %rhs) <{nuw, nsw}> : (i8, i8) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x02#8, 0x02#8, poison, poison]
