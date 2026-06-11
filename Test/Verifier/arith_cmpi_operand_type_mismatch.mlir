// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = () -> i1, sym_name = "main"}> ({
    %lhs = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 5 : i16 }> : () -> i16
    %cmp = "arith.cmpi"(%lhs, %rhs) <{ predicate = 2 : i64 }> : (i8, i16) -> i1
    "func.return"(%cmp) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.cmpi: Expected operands to have the same type
