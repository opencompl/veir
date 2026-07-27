// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i16)}> ({
    %lhs = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %rhs = "arith.constant"() <{value = 5 : i8}> : () -> i8
    %low, %high = "arith.mulsi_extended"(%lhs, %rhs) : (i8, i8) -> (i8, i16)
    "func.return"(%low, %high) : (i8, i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.mulsi_extended: Expected result 1 type to match operand type
