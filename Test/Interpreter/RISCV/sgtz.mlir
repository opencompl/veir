// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 0 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 1 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -1 : i64 }> : () -> !riscv.reg
    %d = "riscv.sgtz"(%a) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.sgtz"(%b) : (!riscv.reg) -> !riscv.reg
    %f = "riscv.sgtz"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%d, %e, %f) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000000#64]
