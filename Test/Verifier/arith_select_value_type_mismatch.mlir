// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> i8, sym_name = "main"}> ({
    %cond = "arith.constant"() <{ "value" = 1 : i1 }> : () -> i1
    %lhs = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 5 : i16 }> : () -> i16
    %sel = "arith.select"(%cond, %lhs, %rhs) : (i1, i8, i16) -> i8
    "func.return"(%sel) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.select: Expected select values to have the same type
