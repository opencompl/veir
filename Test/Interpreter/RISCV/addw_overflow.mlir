// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 4294967296 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.addw"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%c) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000005#64]
