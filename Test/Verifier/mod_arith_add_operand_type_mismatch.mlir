// RUN: not veir-opt %s 2>&1 | filecheck %s

// mismatched moduli (17 vs 19)
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 13 : i32}> : () -> !mod_arith.int<17 : i32>
      %1 = "mod_arith.constant"() <{"value" = 7 : i32}> : () -> !mod_arith.int<19 : i32>
      %2 = "mod_arith.add"(%0, %1) : (!mod_arith.int<17 : i32>, !mod_arith.int<19 : i32>) -> !mod_arith.int<17 : i32>
      "func.return"(%2) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.add: Expected operands to have the same type
