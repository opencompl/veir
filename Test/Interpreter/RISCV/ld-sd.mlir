// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ "value" = 8 : i64 }> : () -> !reg
    %x = "riscv.li"() <{ "value" = 290 : i64 }> : () -> !reg
    "riscv.sd"(%a, %x) <{ "value" = 0 : i64 }> : (!reg, !reg) -> ()
    %y = "riscv.ld"(%a) <{ "value" = 0 : i64 }> : (!reg) -> !reg
    "func.return"(%y) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000122#64]

