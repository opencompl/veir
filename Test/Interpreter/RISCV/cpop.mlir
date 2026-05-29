// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    %a = "riscv.li"() <{ value = 2 : i64 }> : () -> !reg
    %b = "riscv.li"() <{ value = -5 : i64 }> : () -> !reg
    %c = "riscv.li"() <{ value = 4294967298 : i64 }> : () -> !reg
    %d = "riscv.cpop"(%a) : (!reg) -> !reg
    %e = "riscv.cpop"(%b) : (!reg) -> !reg
    %f = "riscv.cpop"(%c) : (!reg) -> !reg
    "func.return"(%d, %e, %f) : (!reg, !reg, !reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64, 0x000000000000003f#64, 0x0000000000000002#64]
