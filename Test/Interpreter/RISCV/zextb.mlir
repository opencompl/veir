// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = -5 : i64 }> : () -> i64
    %b = "riscv.zextb"(%a) : (i64) -> i64
    "func.return"(%b) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000fb#64]
