// RUN: veir-opt %s | filecheck %s

// overly-wide integer attributes in mod_arith.constant are allowed
// as long as the value itself will fit into the mod_arith type's storage type.
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i32>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 13 : i64}> : () -> !mod_arith.int<17 : i32>
      "func.return"(%0) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "mod_arith.constant"() <{"value" = 13 : i64}> : () -> !mod_arith.int<17 : i32>
