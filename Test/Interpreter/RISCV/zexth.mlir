// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %d = "riscv.zexth"(%a) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.zexth"(%b) : (!riscv.reg) -> !riscv.reg
    %f = "riscv.zexth"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%d, %e, %f) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64, 0x000000000000fffb#64, 0x0000000000000002#64]
