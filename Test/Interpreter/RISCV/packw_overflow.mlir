// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !riscv.reg
    %c = "riscv.packw"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%c) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000010002#64]
