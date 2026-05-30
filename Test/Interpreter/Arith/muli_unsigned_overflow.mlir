// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %lhs = "arith.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %none = "arith.muli"(%lhs, %rhs) : (i8, i8) -> i8
    %nsw = "arith.muli"(%lhs, %rhs) <{"overflowFlags" = 1 : i32}> : (i8, i8) -> i8
    %nuw = "arith.muli"(%lhs, %rhs) <{"overflowFlags" = 2 : i32}> : (i8, i8) -> i8
    %nuw_nsw = "arith.muli"(%lhs, %rhs) <{"overflowFlags" = 3 : i32}> : (i8, i8) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfe#8, 0xfe#8, poison, poison]
