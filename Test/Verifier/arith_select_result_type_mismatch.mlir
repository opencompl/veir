// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> i16, sym_name = "main"}> ({
    %cond = "arith.constant"() <{ "value" = 1 : i1 }> : () -> i1
    %lhs = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %sel = "arith.select"(%cond, %lhs, %rhs) : (i1, i8, i8) -> i16
    "func.return"(%sel) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.select: Expected result type to match select value type
