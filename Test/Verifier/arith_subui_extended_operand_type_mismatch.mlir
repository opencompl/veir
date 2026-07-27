// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1)}> ({
    %lhs = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %rhs = "arith.constant"() <{value = 5 : i16}> : () -> i16
    %diff, %borrow = "arith.subui_extended"(%lhs, %rhs) : (i8, i16) -> (i8, i1)
    "func.return"(%diff, %borrow) : (i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.subui_extended: Expected operands to have the same type
