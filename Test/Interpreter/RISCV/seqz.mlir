// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 0 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 1 : i64 }> : () -> !riscv.reg
    %c = "riscv.seqz"(%a) : (!riscv.reg) -> !riscv.reg
    %d = "riscv.seqz"(%b) : (!riscv.reg) -> !riscv.reg
    "func.return"(%c, %d) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
