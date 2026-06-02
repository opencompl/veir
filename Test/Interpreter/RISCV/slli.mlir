// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = 29 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %d = "riscv.slli"(%a) <{ value = 3 : i6 }> : (!reg) -> !reg
    %e = "riscv.slli"(%b) <{ value = -3 : i6 }> : (!reg) -> !reg
    %f = "riscv.slli"(%c) <{ value = -3 : i5 }> : (!reg) -> !reg
    "func.return"(%d, %e, %f) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffd8#64, 0xa000000000000000#64, 0x4000000000000000#64]