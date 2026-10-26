// RUN: not veir-opt %s 2>&1 | filecheck %s

// 7 does *not* fit into ui2, so the parser rejects the modulus.
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<7 : ui2>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 1 : ui2}> : () -> !mod_arith.int<7 : ui2>
      "func.return"(%0) : (!mod_arith.int<7 : ui2>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: integer constant out of range for attribute
