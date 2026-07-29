// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<17 : i32>}> ({
    %c3 = "mod_arith.constant"() <{ "value" = 3 : i32 }> : () -> !mod_arith.int<17 : i32>
    "func.return"(%c3) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32]
