// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<17 : i32>}> ({
    %c = "mod_arith.constant"() <{ "value" = -3 : i32 }> : () -> !mod_arith.int<17 : i32>
    "func.return"(%c) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// -3 mod 17 = 14
// CHECK: Program output: #[0x0000000e#32]
