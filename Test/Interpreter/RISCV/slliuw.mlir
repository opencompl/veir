// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 29 : i64 }> : () -> !riscv.reg
    %b = "riscv.slliuw"(%a) <{ value = 3 : i5 }> : (!riscv.reg) -> !riscv.reg
    %c = "riscv.li"() <{ value = 29 : i64 }> : () -> !riscv.reg
    %d = "riscv.slliuw"(%c) <{ value = -3 : i5 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b, %d) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000000000e8#64, 0xa000000000000000#64]
