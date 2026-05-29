// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %d = "riscv.rori"(%a) <{ value = 3 : i6 }> : (!reg) -> !reg
    %e = "riscv.rori"(%b) <{ value = -3 : i6 }> : (!reg) -> !reg
    %f = "riscv.rori"(%c) <{ value = -3 : i6 }> : (!reg) -> !reg
    "func.return"(%d, %e, %f) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xa000000000000003#64, 0x00000000000000e8#64, 0x0000000800000010#64]
