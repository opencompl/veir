// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i16, i8)}> ({
    %lhs = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %rhs = "arith.constant"() <{value = 5 : i8}> : () -> i8
    %low, %high = "arith.mului_extended"(%lhs, %rhs) : (i8, i8) -> (i16, i8)
    "func.return"(%low, %high) : (i16, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.mului_extended: Expected result 0 type to match operand type
