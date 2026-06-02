// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %c = "riscv.binvi"(%a) <{ value = 2 : i12 }> : (!reg) -> !reg
    %d = "riscv.binvi"(%b) <{ value = 5 : i12 }> : (!reg) -> !reg
    "func.return"(%c, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000006#64, 0xffffffffffffffdb#64]
