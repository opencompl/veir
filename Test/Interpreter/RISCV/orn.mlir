// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 53 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = -2 : i64 }> : () -> !reg
    %d = "riscv.orn"(%a, %b) : (!reg, !reg) -> !reg
    %e = "riscv.orn"(%a, %c) : (!reg, !reg) -> !reg
    "func.return"(%d, %e) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xfffffffffffffffd#64, 0x0000000000000035#64]
