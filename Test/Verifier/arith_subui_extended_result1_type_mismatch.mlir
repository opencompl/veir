// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %lhs = "arith.constant"() <{value = 3 : i8}> : () -> i8
    %rhs = "arith.constant"() <{value = 5 : i8}> : () -> i8
    %diff, %borrow = "arith.subui_extended"(%lhs, %rhs) : (i8, i8) -> (i8, i8)
    "func.return"(%diff, %borrow) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.subui_extended: Expected i1 result 1
