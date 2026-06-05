// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %x = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %y = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %z = "riscv.addw"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64]
