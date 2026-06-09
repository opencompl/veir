// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %cond = "arith.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %lhs = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %sel = "arith.select"(%cond, %lhs, %rhs) : (i8, i8, i8) -> i8
    "func.return"(%sel) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.select: Expected i1 condition
