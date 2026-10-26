// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<251 : ui8>}> ({
    %lhs = "mod_arith.constant"() <{ "value" = 250 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %rhs = "mod_arith.constant"() <{ "value" = 1 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %diff = "mod_arith.sub"(%lhs, %rhs) : (!mod_arith.int<251 : ui8>, !mod_arith.int<251 : ui8>) -> !mod_arith.int<251 : ui8>
    "func.return"(%diff) : (!mod_arith.int<251 : ui8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xf9#8]
