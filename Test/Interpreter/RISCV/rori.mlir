// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 29 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 29 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %d = "riscv.rori"(%a) <{ value = 3 : i6 }> : (!riscv.reg) -> !riscv.reg
    %e = "riscv.rori"(%b) <{ value = 61 : i6 }> : (!riscv.reg) -> !riscv.reg
    %f = "riscv.rori"(%c) <{ value = 61 : i6 }> : (!riscv.reg) -> !riscv.reg
    "func.return"(%d, %e, %f) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xa000000000000003#64, 0x00000000000000e8#64, 0x0000000800000010#64]
