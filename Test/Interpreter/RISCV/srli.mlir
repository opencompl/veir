// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 11 : i64 }> : () -> !riscv.reg
    %b = "riscv.srli"(%a) <{ value = 3 : i6 }> : (!riscv.reg) -> !riscv.reg
    %c = "riscv.li"() <{ value = 11 : i64 }> : () -> !riscv.reg
    %d = "riscv.srli"(%c) <{ value = -3 : i6 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b, %d) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x0000000000000000#64]
