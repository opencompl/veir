// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %e = "riscv.rol"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %f = "riscv.rol"(%a, %d) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.rol"(%c, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%e, %f, %g) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000040#64, 0x1000000000000000#64, 0x0000002000000040#64]
