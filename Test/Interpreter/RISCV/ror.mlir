// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (!riscv.reg, !riscv.reg, !riscv.reg)}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %e = "riscv.ror"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %f = "riscv.ror"(%a, %d) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.ror"(%c, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%e, %f, %g) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1000000000000000#64, 0x0000000000000040#64, 0x1000000008000000#64]
