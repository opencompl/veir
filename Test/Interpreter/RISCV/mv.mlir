// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %b = "riscv.mv"(%a) : (!reg) -> !reg
    "func.return"(%b) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64]
