// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %d = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %e = "riscv.ror"(%a, %b) : (!reg, !reg) -> !reg
    %f = "riscv.ror"(%a, %d) : (!reg, !reg) -> !reg
    %g = "riscv.ror"(%c, %b) : (!reg, !reg) -> !reg
    "func.return"(%e, %f, %g) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1000000000000000#64, 0x0000000000000040#64, 0x1000000008000000#64]
