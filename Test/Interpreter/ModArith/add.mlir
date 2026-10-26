// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : ui8>}> ({
    %lhs = "mod_arith.constant"() <{ "value" = 250 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %rhs = "mod_arith.constant"() <{ "value" = 10 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %sum = "mod_arith.add"(%lhs, %rhs) : (!mod_arith.int<251 : ui8>, !mod_arith.int<251 : ui8>) -> !mod_arith.int<251 : ui8>
    "func.return"(%sum) : (!mod_arith.int<251 : ui8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x09#8]
