// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : ui8>}> ({
    %lhs = "mod_arith.constant"() <{ "value" = 250 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %rhs = "mod_arith.constant"() <{ "value" = 250 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %product = "mod_arith.mul"(%lhs, %rhs) : (!mod_arith.int<251 : ui8>, !mod_arith.int<251 : ui8>) -> !mod_arith.int<251 : ui8>
    "func.return"(%product) : (!mod_arith.int<251 : ui8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x01#8]
