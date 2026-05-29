// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %d = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !reg
    %e = "riscv.pack"(%a, %b) : (!reg, !reg) -> !reg
    %f = "riscv.pack"(%a, %c) : (!reg, !reg) -> !reg
    %g = "riscv.pack"(%a, %d) : (!reg, !reg) -> !reg
    "func.return"(%e, %f, %g) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000500000002#64, 0xfffffffb00000002#64, 0x0000000100000002#64]
