// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.addi"(%a) <{ value = 5 : i12 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %d = "riscv.addi"(%c) <{ value = -5 : i12 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64, 0xfffffffffffffffd#64]
