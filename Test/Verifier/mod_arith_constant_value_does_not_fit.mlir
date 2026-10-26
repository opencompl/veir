// RUN: not veir-opt %s 2>&1 | filecheck %s

// constant value 300 does not fit in ui8.
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : ui8>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 300 : ui16}> : () -> !mod_arith.int<17 : ui8>
      "func.return"(%0) : (!mod_arith.int<17 : ui8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.constant: constant value 300 does not fit in storage type 'ui8'
