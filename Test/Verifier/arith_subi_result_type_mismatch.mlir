// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i16}> ({
    %lhs = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %rhs = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %sum = "arith.subi"(%lhs, %rhs) : (i8, i8) -> i16
    "func.return"(%sum) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.subi: Expected result type to match operand type
