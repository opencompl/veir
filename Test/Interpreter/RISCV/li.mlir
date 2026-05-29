// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %x = "riscv.li"() <{ "value" = 3 : i64 }> : () -> !reg
    %y = "riscv.li"() <{ "value" = -2 : i64 }> : () -> !reg
    "func.return"(%x, %y) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000003#64, 0xfffffffffffffffe#64]

