// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %x = "riscv.li"() <{ value = 6 : i64 }> : () -> !reg
    %y = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %z = "riscv.and"(%x, %y) : (!reg, !reg) -> !reg
    "func.return"(%z) : (!reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64]
