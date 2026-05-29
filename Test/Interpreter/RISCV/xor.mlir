// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 5 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 7 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 7 : i64 }> : () -> !reg
    %d = "riscv.xor"(%a, %b) : (!reg, !reg) -> !reg
    %e = "riscv.xor"(%a, %c) : (!reg, !reg) -> !reg
    "func.return"(%d, %e) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64, 0x0000000000000002#64]
