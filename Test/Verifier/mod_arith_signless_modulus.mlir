// RUN: not veir-opt %s 2>&1 | filecheck %s

// mod_arith moduli must have an unsigned integer type.
"builtin.module"() ({
  "func.func"() <{function_type = () -> !mod_arith.int<17 : i8>, sym_name = "main"}> ({
    ^bb0():
      %0 = "mod_arith.constant"() <{"value" = 1 : ui8}> : () -> !mod_arith.int<17 : i8>
      "func.return"(%0) : (!mod_arith.int<17 : i8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: mod_arith.constant: Expected result to have ModArithType
// CHECK-SAME: modulus type 'i8' must be an unsigned integer type such as 'ui8'
