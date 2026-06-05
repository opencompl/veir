// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg)}> ({
    %x = "riscv.lui"() <{ value = -5 : i20 }> : () -> !riscv.reg
    %y = "riscv.lui"() <{ value = 3 : i20 }> : () -> !riscv.reg
    "func.return"(%x, %y) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffb000#64, 0x0000000000003000#64]
