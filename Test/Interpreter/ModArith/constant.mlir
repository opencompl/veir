// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<17 : ui32>}> ({
    %c3 = "mod_arith.constant"() <{ "value" = 3 : ui32 }> : () -> !mod_arith.int<17 : ui32>
    "func.return"(%c3) : (!mod_arith.int<17 : ui32>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000003#32]
