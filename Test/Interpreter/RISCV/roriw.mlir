// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %b = "riscv.roriw"(%a) <{ value = 3 : i6 }> : (!reg) -> !reg
    %c = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %d = "riscv.roriw"(%c) <{ value = -3 : i6 }> : (!reg) -> !reg
    "func.return"(%b, %d) : (!reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffa0000003#64, 0x00000000000000e8#64]
