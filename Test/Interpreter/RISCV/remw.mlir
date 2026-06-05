// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %d = "riscv.remw"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %e = "riscv.remw"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%d, %e) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64, 0x0000000000000002#64]
