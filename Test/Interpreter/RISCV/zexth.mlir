// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %d = "riscv.zexth"(%a) : (!reg) -> !reg
    %e = "riscv.zexth"(%b) : (!reg) -> !reg
    %f = "riscv.zexth"(%c) : (!reg) -> !reg
    "func.return"(%d, %e, %f) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000002#64, 0x000000000000fffb#64, 0x0000000000000002#64]
