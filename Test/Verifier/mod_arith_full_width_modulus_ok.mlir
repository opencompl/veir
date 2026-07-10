// RUN: veir-opt %s | filecheck %s

// 7 *just* fits into i3, so also fine (deliberate deviation from HEIR,
// which would require the storage type to be one bit wider than the modulus)
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<7 : i3>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 5 : i3}> : () -> !mod_arith.int<7 : i3>
      %1 = "mod_arith.constant"() <{"value" = 4 : i3}> : () -> !mod_arith.int<7 : i3>
      %2 = "mod_arith.add"(%0, %1) : (!mod_arith.int<7 : i3>, !mod_arith.int<7 : i3>) -> !mod_arith.int<7 : i3>
      "func.return"(%2) : (!mod_arith.int<7 : i3>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "mod_arith.add"(%{{.*}}, %{{.*}}) : (!mod_arith.int<7 : i3>, !mod_arith.int<7 : i3>) -> !mod_arith.int<7 : i3>
