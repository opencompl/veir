// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %lhs = "arith.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 100 : i8 }> : () -> i8
    %none = "arith.addi"(%lhs, %rhs) : (i8, i8) -> i8
    %nsw = "arith.addi"(%lhs, %rhs) <{"overflowFlags" = #arith.overflow<nsw>}> : (i8, i8) -> i8
    %nuw = "arith.addi"(%lhs, %rhs) <{"overflowFlags" = #arith.overflow<nuw>}> : (i8, i8) -> i8
    %nuw_nsw = "arith.addi"(%lhs, %rhs) <{"overflowFlags" = #arith.overflow<nsw, nuw>}> : (i8, i8) -> i8
    "func.return"(%none, %nsw, %nuw, %nuw_nsw) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xc8#8, poison, 0xc8#8, poison]
