// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %b = "riscv.zextb"(%a) : (!reg) -> !reg
    "func.return"(%b) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000fb#64]
