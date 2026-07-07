// RUN: not veir-opt %s 2>&1 | filecheck %s

// 7 does *not* fit into i2
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<7 : i2>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 1 : i2}> : () -> !mod_arith.int<7 : i2>
      "func.return"(%0) : (!mod_arith.int<7 : i2>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: modulus 7 does not fit into the underlying storage type 'i2'
