// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> !mod_arith.int<17 : i32>}> ({
    %c = "mod_arith.constant"() <{ "value" = -3 : i32 }> : () -> !mod_arith.int<17 : i32>
    "func.return"(%c) : (!mod_arith.int<17 : i32>) -> ()
  }) : () -> ()
}) : () -> ()

// -3 mod 17 = 14
// A residue is unsigned, and so is the attribute that names one: `-3 : i32`
// and `4294967293 : i32` are the same attribute, so the residue is
// 4294967293 mod 17 = 15 rather than -3 mod 17 = 14.
// CHECK: Program output: #[0x0000000f#32]
