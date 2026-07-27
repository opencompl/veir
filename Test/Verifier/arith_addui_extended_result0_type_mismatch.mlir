// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i16, i1)}> ({
    %lhs = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %rhs = "arith.constant"() <{value = 5 : i8}> : () -> i8
    %sum, %carry = "arith.addui_extended"(%lhs, %rhs) : (i8, i8) -> (i16, i1)
    "func.return"(%sum, %carry) : (i16, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.addui_extended: Expected result 0 type to match operand type
