// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 7 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 7 : i64 }> : () -> !reg
    %d = "riscv.xnor"(%a, %b) : (!reg, !reg) -> !reg
    %e = "riscv.xnor"(%a, %c) : (!reg, !reg) -> !reg
    "func.return"(%d, %e) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffd#64, 0xfffffffffffffffd#64]
