// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %c = "arith.constant"() <{ "value" = 18446744073709551616 : i66 }> : () -> i66
    %none = "arith.shli"(%c, %c) : (i66, i66) -> i66
    %nsw = "arith.shli"(%c, %c) <{"overflowFlags" = 1 : i32}> : (i66, i66) -> i66
    %nuw = "arith.shli"(%c, %c) <{"overflowFlags" = 2 : i32}> : (i66, i66) -> i66
    %nsw_nuw = "arith.shli"(%c, %c) <{"overflowFlags" = 3 : i32}> : (i66, i66) -> i66
    "func.return"(%none, %nsw, %nuw, %nsw_nuw) : (i66, i66, i66, i66) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison, poison, poison]
