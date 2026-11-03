// RUN: not veir-opt %s 2>&1 | filecheck %s

// constant value 300 does not fit in i8.
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i8>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 300 : i16}> : () -> !mod_arith.int<17 : i8>
      "func.return"(%0) : (!mod_arith.int<17 : i8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.constant: constant value 300 does not fit in storage type 'i8'
