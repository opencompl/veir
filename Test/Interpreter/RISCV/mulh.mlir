// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !riscv.reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !riscv.reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !riscv.reg
    %d = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !riscv.reg
    %e = "riscv.li"() <{ value = -3 : i64 }> : () -> !riscv.reg
    %f = "riscv.mulh"(%a, %b) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %g = "riscv.mulh"(%a, %c) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %h = "riscv.mulh"(%d, %e) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%f, %g, %h) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64, 0xffffffffffffffff#64, 0xffffffffffffffff#64]
