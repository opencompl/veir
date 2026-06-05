// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.auipc"(%a) <{ value = 3 : i20 }> : (!riscv.reg) -> !riscv.reg
    %c = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %d = "riscv.auipc"(%c) <{ value = -3 : i20 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%b, %d) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000003002#64, 0xffffffffffffd002#64]
