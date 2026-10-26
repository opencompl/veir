// RUN: veir-interpret %s | filecheck %s

// Integer attributes are normalized as in MLIR: `200 : ui8` is 200, while the
// signless `200 : i8` is -56, which is 195 mod 251.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!mod_arith.int<251 : ui8>, !mod_arith.int<251 : ui8>)}> ({
    %u = "mod_arith.constant"() <{ "value" = 200 : ui8 }> : () -> !mod_arith.int<251 : ui8>
    %s = "mod_arith.constant"() <{ "value" = 200 : i8 }> : () -> !mod_arith.int<251 : ui8>
    "func.return"(%u, %s) : (!mod_arith.int<251 : ui8>, !mod_arith.int<251 : ui8>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xc8#8, 0xc3#8]
