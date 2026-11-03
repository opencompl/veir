// RUN: veir-interpret %s | filecheck %s

// Regression check: a poison dividend with a concrete safe (nonzero) divisor
// propagates as poison — NOT immediate UB.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i32}> ({
    %five = "arith.constant"() <{ "value" = 5 : i32 }> : () -> i32
    %neg1 = "arith.constant"() <{ "value" = -1 : i32 }> : () -> i32
    %one  = "arith.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %poison = "arith.addi"(%neg1, %one) <{"overflowFlags" = #arith.overflow<nuw>}> : (i32, i32) -> i32
    %y = "arith.divui"(%poison, %five) : (i32, i32) -> i32
    "func.return"(%y) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
