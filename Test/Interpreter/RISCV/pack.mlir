// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !riscv.reg
    %e = "riscv.pack"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %f = "riscv.pack"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.pack"(%a, %d) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%e, %f, %g) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000500000002#64, 0xfffffffb00000002#64, 0x0000000100000002#64]
