// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %c = "riscv.bexti"(%a) <{ value = 2 : i12 }> : (!riscv.reg) -> !riscv.reg
    %d = "riscv.bexti"(%b) <{ value = 5 : i12 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%c, %d) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000001#64]
