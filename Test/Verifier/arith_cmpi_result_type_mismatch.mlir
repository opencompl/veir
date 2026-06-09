// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %lhs = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %cmp = "arith.cmpi"(%lhs, %rhs) <{ predicate = 2 : i64 }> : (i8, i8) -> i8
    "func.return"(%cmp) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.cmpi: Expected i1 result
