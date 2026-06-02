// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %d = "riscv.li"() <{ value = 4294967297 : i64 }> : () -> !reg
    %e = "riscv.packh"(%a, %b) : (!reg, !reg) -> !reg
    %f = "riscv.packh"(%a, %c) : (!reg, !reg) -> !reg
    %g = "riscv.packh"(%a, %d) : (!reg, !reg) -> !reg
    "func.return"(%e, %f, %g) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000502#64, 0x000000000000fb02#64, 0x0000000000000102#64]
