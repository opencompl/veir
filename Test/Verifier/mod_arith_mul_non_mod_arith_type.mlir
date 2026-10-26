// RUN: not veir-opt %s 2>&1 | filecheck %s

// return type is not a mod_arith type
"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 13 : ui32}> : () -> !mod_arith.int<17 : ui32>
      %1 = "mod_arith.constant"() <{"value" = 7 : ui32}> : () -> !mod_arith.int<17 : ui32>
      %2 = "mod_arith.mul"(%0, %1) : (!mod_arith.int<17 : ui32>, !mod_arith.int<17 : ui32>) -> i32
      "func.return"(%2) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.mul: Expected result type to match operand type
